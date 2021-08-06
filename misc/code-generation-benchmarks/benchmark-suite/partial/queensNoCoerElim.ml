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
      SolutionsCons
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           (_x_55, _op_44 (* @ *) _xs_54 _ys_53))

let _op_44 (* @ *) = _op_44 (* @ *)

let _no_attack_58 ((_x_59, _y_60) : int * int) ((_x'_61, _y'_62) : int * int) =
  _x_59 <> _x'_61 && _y_60 <> _y'_62
  && abs (_x_59 - _x'_61) <> abs (_y_60 - _y'_62)

let no_attack = _no_attack_58

let rec _not_attacked_74 _x_82 (_qs_76 : solution) =
  match _qs_76 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_77, _xs_78) ->
      _no_attack_58
        (coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_82)
        (coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_77)
      && _not_attacked_74
           (coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_82)
           _xs_78

let not_attacked = _not_attacked_74

let _available_83 (_number_of_queens_84 : int) (_x_85 : int) (_qs_86 : solution)
    =
  let rec _loop_87 _x_98 =
    let _possible_88, _y_89 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_98 in
    if _y_89 < 1 then _possible_88
    else if
      _not_attacked_74
        (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_x_85, _y_89))
        _qs_86
    then
      _loop_87
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           ( RowsCons
               (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_y_89, _possible_88)),
             _y_89 - 1 ))
    else
      _loop_87
        (coer_tuple_2 (coer_refl_ty, coer_refl_ty) (_possible_88, _y_89 - 1))
  in
  _loop_87
    (coer_tuple_2
       (coer_refl_ty, coer_refl_ty)
       (RowsEmpty, _number_of_queens_84))

let available = _available_83

let rec _choose_99 _x_109 =
  match _x_109 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_117 : empty) ->
            coer_computation coer_refl_ty
              (coer_return coer_refl_ty (match _y_117 with _ -> assert false))
        )
  | RowsCons (_x_119, _xs'_118) ->
      Call
        ( Decide,
          (),
          fun (_y_120 : bool) ->
            if _y_120 then coer_return coer_refl_ty _x_119
            else _choose_99 _xs'_118 )

let choose = _choose_99

let _queens_121 (_number_of_queens_122 : int) =
  let rec _place_123 _x_134 =
    let _x_124, _qs_125 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_134 in
    coer_return coer_refl_ty (( > ) _x_124) >>= fun _b_127 ->
    coer_return coer_refl_ty (_b_127 _number_of_queens_122) >>= fun _b_126 ->
    if _b_126 then coer_return coer_refl_ty _qs_125
    else
      coer_return coer_refl_ty (_available_83 _number_of_queens_122)
      >>= fun _b_131 ->
      coer_return coer_refl_ty (_b_131 _x_124) >>= fun _b_130 ->
      coer_return coer_refl_ty (_b_130 _qs_125) >>= fun _b_129 ->
      _choose_99 _b_129 >>= fun _y_128 ->
      coer_return coer_refl_ty (( + ) _x_124) >>= fun _b_133 ->
      coer_return coer_refl_ty (_b_133 1) >>= fun _b_132 ->
      _place_123
        (coer_tuple_2
           (coer_refl_ty, coer_refl_ty)
           ( _b_132,
             SolutionPlace
               (coer_tuple_2
                  (coer_tuple_2 (coer_refl_ty, coer_refl_ty), coer_refl_ty)
                  ((_x_124, _y_128), _qs_125)) ))
  in
  _place_123 (1, SolutionEmpty)

let queens = _queens_121

let _queens_one_option_135 (_number_of_queens_136 : int) =
  let rec _queens_149 _number_of_queens_122 =
    let rec _place_123 _x_134 =
      let _x_124, _qs_125 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_134 in
      coer_return coer_refl_ty (( > ) _x_124) >>= fun _b_127 ->
      coer_return coer_refl_ty (_b_127 _number_of_queens_122) >>= fun _b_126 ->
      if _b_126 then coer_return coer_refl_ty _qs_125
      else
        coer_return coer_refl_ty (_available_83 _number_of_queens_122)
        >>= fun _b_131 ->
        coer_return coer_refl_ty (_b_131 _x_124) >>= fun _b_130 ->
        coer_return coer_refl_ty (_b_130 _qs_125) >>= fun _b_129 ->
        _choose_99 _b_129 >>= fun _y_128 ->
        coer_return coer_refl_ty (( + ) _x_124) >>= fun _b_133 ->
        coer_return coer_refl_ty (_b_133 1) >>= fun _b_132 ->
        _place_123
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             ( _b_132,
               SolutionPlace
                 (coer_tuple_2
                    (coer_tuple_2 (coer_refl_ty, coer_refl_ty), coer_refl_ty)
                    ((_x_124, _y_128), _qs_125)) ))
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x_142 : solution) -> Value (Some _x_142));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Decide ->
                    fun _ _l_145 ->
                      Value
                        (match
                           coer_arrow coer_refl_ty force_unsafe _l_145 true
                         with
                        | Some _x_140 -> Some _x_140
                        | None ->
                            coer_arrow coer_refl_ty force_unsafe _l_145 false)
                | Fail -> fun _ _l_146 -> Value None
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (_place_123 (1, SolutionEmpty)))
  in
  _queens_149 _number_of_queens_136

let queens_one_option = _queens_one_option_135

let _queens_all_150 (_number_of_queens_151 : int) =
  let rec _queens_165 _number_of_queens_122 =
    let rec _place_123 _x_134 =
      let _x_124, _qs_125 = coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_134 in
      coer_return coer_refl_ty (( > ) _x_124) >>= fun _b_127 ->
      coer_return coer_refl_ty (_b_127 _number_of_queens_122) >>= fun _b_126 ->
      if _b_126 then coer_return coer_refl_ty _qs_125
      else
        coer_return coer_refl_ty (_available_83 _number_of_queens_122)
        >>= fun _b_131 ->
        coer_return coer_refl_ty (_b_131 _x_124) >>= fun _b_130 ->
        coer_return coer_refl_ty (_b_130 _qs_125) >>= fun _b_129 ->
        _choose_99 _b_129 >>= fun _y_128 ->
        coer_return coer_refl_ty (( + ) _x_124) >>= fun _b_133 ->
        coer_return coer_refl_ty (_b_133 1) >>= fun _b_132 ->
        _place_123
          (coer_tuple_2
             (coer_refl_ty, coer_refl_ty)
             ( _b_132,
               SolutionPlace
                 (coer_tuple_2
                    (coer_tuple_2 (coer_refl_ty, coer_refl_ty), coer_refl_ty)
                    ((_x_124, _y_128), _qs_125)) ))
    in
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x_158 : solution) ->
                Value
                  (SolutionsCons
                     (coer_tuple_2
                        (coer_refl_ty, coer_refl_ty)
                        (_x_158, SolutionsNil))));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Decide ->
                    fun _ _l_161 ->
                      Value
                        (_op_44 (* @ *)
                           (coer_arrow coer_refl_ty force_unsafe _l_161 true)
                           (coer_arrow coer_refl_ty force_unsafe _l_161 false))
                | Fail -> fun _ _l_162 -> Value SolutionsNil
                | eff' -> fun arg k -> Call (eff', arg, k));
          })
         (_place_123 (1, SolutionEmpty)))
  in
  _queens_165 _number_of_queens_151

let queens_all = _queens_all_150

let _queens_one_cps_166 (_number_of_queens_167 : int) =
  coer_return coer_refl_ty
    (let rec _queens_197 _number_of_queens_198 =
       let rec _place_324 _x_200 =
         let _x_202, _qs_201 =
           coer_tuple_2 (coer_refl_ty, coer_refl_ty) _x_200
         in
         if _x_202 > _number_of_queens_198 then
           coer_arrow
             (coer_arrow coer_refl_ty (coer_computation coer_refl_ty))
             (coer_return coer_refl_ty)
             (fun (_ : unit -> solution computation) -> _qs_201)
         else
           let rec _choose_414 _x_415 =
             match _x_415 with
             | RowsEmpty ->
                 fun (_kf_416 : unit -> solution computation) -> _kf_416 ()
             | RowsCons (_x_418, _xs'_417) ->
                 let _l_419 (_y_423 : bool) =
                   if _y_423 then
                     _place_324
                       (coer_tuple_2
                          (coer_refl_ty, coer_refl_ty)
                          ( _x_202 + 1,
                            SolutionPlace
                              (coer_tuple_2
                                 ( coer_tuple_2 (coer_refl_ty, coer_refl_ty),
                                   coer_refl_ty )
                                 ((_x_202, _x_418), _qs_201)) ))
                   else _choose_414 _xs'_417
                 in
                 fun (_kf_420 : unit -> solution computation) ->
                   coer_return coer_refl_ty (_l_419 true) >>= fun _b_421 ->
                   _b_421
                     (coer_arrow coer_refl_ty (coer_computation coer_refl_ty)
                        (fun (_ : unit) ->
                          coer_return coer_refl_ty (_l_419 false)
                          >>= fun _b_422 ->
                          _b_422
                            (coer_arrow coer_refl_ty
                               (coer_computation coer_refl_ty)
                               _kf_420)))
           in
           _choose_414 (_available_83 _number_of_queens_198 _x_202 _qs_201)
       in
       _place_324 (1, SolutionEmpty)
     in
     _queens_197 _number_of_queens_167)
  >>= fun _b_195 ->
  _b_195
    (coer_arrow coer_refl_ty (coer_computation coer_refl_ty) (fun (() : unit) ->
         Call
           ( Fail,
             (),
             fun (_y_196 : empty) ->
               coer_return coer_refl_ty (match _y_196 with _ -> assert false) )))

let queens_one_cps = _queens_one_cps_166
