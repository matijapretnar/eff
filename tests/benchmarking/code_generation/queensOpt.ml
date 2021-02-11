open OcamlHeader

let _op_0 (* < *) = ( < )

let _op_1 (* = *) = ( = )

let _op_2 (* - *) = ( - )

let _op_3 (* + *) = ( + )

let _op_4 (* ~- *) = ( ~- )

type (_, _) effect += Decide : (unit, bool) effect

type (_, _) effect += Fail : (unit, empty) effect

type queen = Queen of (int * int)

type rows = RowsEmpty | RowsCons of (int * rows)

type solution = SolutionEmpty | SolutionPlace of (queen * solution)

type solutions = SolutionsNil | SolutionsCons of (solution * solutions)

type optional_solution = None | Some of solution

type void = Void

let _absurd_5 (_void_6 : float) = match _void_6 with _ -> assert false

let absurd = _absurd_5

let rec _op_7 (* @ *) _x_14 (_ys_16 : solutions) =
  match _x_14 with
  | SolutionsNil -> _ys_16
  | SolutionsCons (_x_18, _xs_17) ->
      SolutionsCons (_x_18, _op_7 (* @ *) _xs_17 _ys_16)

let _op_7 (* @ *) = _op_7 (* @ *)

let _op_21 (* > *) (_x_22 : int) (_y_23 : int) = _op_0 (* < *) _y_23 _x_22

let _op_21 (* > *) = _op_21 (* > *)

let _op_25 (* <> *) (_x_26 : int) (_y_27 : int) =
  match _op_1 (* = *) _y_27 _x_26 with true -> false | false -> true

let _op_25 (* <> *) = _op_25 (* <> *)

let _abs_30 (_x_31 : int) =
  match _op_0 (* < *) _x_31 0 with
  | true -> _op_4 (* ~- *) _x_31
  | false -> _x_31

let abs = _abs_30

let _no_attack_34 (_q1_35 : queen) (_q2_36 : queen) =
  match _q1_35 with
  | Queen (_x_37, _y_38) -> (
      match _q2_36 with
      | Queen (_x'_39, _y'_40) -> (
          match _op_25 (* <> *) _x_37 _x'_39 with
          | true -> (
              match _op_25 (* <> *) _y_38 _y'_40 with
              | true ->
                  _op_25 (* <> *)
                    (_abs_30 (_op_2 (* - *) _x_37 _x'_39))
                    (_abs_30 (_op_2 (* - *) _y_38 _y'_40))
              | false -> false
              | false -> false)))

let no_attack = _no_attack_34

let rec _not_attacked_52 _x_60 (_qs_62 : solution) =
  match _qs_62 with
  | SolutionEmpty -> true
  | SolutionPlace (_x_64, _xs_63) -> (
      match _no_attack_34 _x_60 _x_64 with
      | true -> _not_attacked_52 _x_60 _xs_63
      | false -> false)

let not_attacked = _not_attacked_52

let _available_68 (_number_of_queens_69 : int) (_x_70 : int) (_qs_71 : solution)
    =
  let rec _loop_72 _x_83 =
    let _possible_73, _y_74 = _x_83 in
    match _op_0 (* < *) _y_74 1 with
    | true -> _possible_73
    | false -> (
        match _not_attacked_52 (Queen (_x_70, _y_74)) _qs_71 with
        | true ->
            _loop_72 (RowsCons (_y_74, _possible_73), _op_2 (* - *) _y_74 1)
        | false -> _loop_72 (_possible_73, _op_2 (* - *) _y_74 1))
  in
  _loop_72 (RowsEmpty, _number_of_queens_69)

let available = _available_68

let rec _tr_choose_94 _x_104 =
  match _x_104 with
  | RowsEmpty ->
      Call
        ( Fail,
          (),
          fun (_y_112 : empty) -> Value (match _y_112 with _ -> assert false) )
  | RowsCons (_x_114, _xs'_113) ->
      Call
        ( Decide,
          (),
          fun (_y_115 : bool) ->
            match _y_115 with
            | true -> Value _x_114
            | false -> _tr_choose_94 _xs'_113 )

let tr_choose = _tr_choose_94

let _queens_116 (_number_of_queens_117 : int) =
  let rec _tr_place_118 _x_129 =
    let _x_119, _qs_120 = _x_129 in
    match _op_21 (* > *) _x_119 _number_of_queens_117 with
    | true -> Value _qs_120
    | false ->
        _tr_choose_94 (_available_68 _number_of_queens_117 _x_119 _qs_120)
        >> fun _y_123 ->
        _tr_place_118
          ( _op_3 (* + *) _x_119 1,
            SolutionPlace (Queen (_x_119, _y_123), _qs_120) )
  in
  _tr_place_118 (1, SolutionEmpty)

let queens = _queens_116

let _queens_one_option_140 (_number_of_queens_141 : int) =
  let rec _queens_154 _number_of_queens_117 =
    let rec _tr_place_118 _x_129 =
      let _x_119, _qs_120 = _x_129 in
      match _op_21 (* > *) _x_119 _number_of_queens_117 with
      | true -> Value _qs_120
      | false ->
          _tr_choose_94 (_available_68 _number_of_queens_117 _x_119 _qs_120)
          >> fun _y_123 ->
          _tr_place_118
            ( _op_3 (* + *) _x_119 1,
              SolutionPlace (Queen (_x_119, _y_123), _qs_120) )
    in
    let rec _tr_place_165 _x_129 =
      let _x_119, _qs_120 = _x_129 in
      match _op_21 (* > *) _x_119 _number_of_queens_117 with
      | true -> Some _qs_120
      | false ->
          let rec _tr_choose_167 _x_104 =
            match _x_104 with
            | RowsEmpty -> None
            | RowsCons (_x_114, _xs'_113) -> (
                let _l_150 (_y_115 : bool) =
                  match _y_115 with
                  | true ->
                      _tr_place_165
                        ( _op_3 (* + *) _x_119 1,
                          SolutionPlace (Queen (_x_119, _x_114), _qs_120) )
                  | false -> _tr_choose_167 _xs'_113
                in
                match _l_150 true with
                | Some _x_145 -> Some _x_145
                | None -> _l_150 false)
          in
          _tr_choose_167 (_available_68 _number_of_queens_117 _x_119 _qs_120)
    in
    _tr_place_165 (1, SolutionEmpty)
  in
  _queens_154 _number_of_queens_141

let queens_one_option = _queens_one_option_140

let _queens_all_188 (_number_of_queens_189 : int) =
  let rec _queens_203 _number_of_queens_117 =
    let rec _tr_place_118 _x_129 =
      let _x_119, _qs_120 = _x_129 in
      match _op_21 (* > *) _x_119 _number_of_queens_117 with
      | true -> Value _qs_120
      | false ->
          _tr_choose_94 (_available_68 _number_of_queens_117 _x_119 _qs_120)
          >> fun _y_123 ->
          _tr_place_118
            ( _op_3 (* + *) _x_119 1,
              SolutionPlace (Queen (_x_119, _y_123), _qs_120) )
    in
    let rec _tr_place_214 _x_129 =
      let _x_119, _qs_120 = _x_129 in
      match _op_21 (* > *) _x_119 _number_of_queens_117 with
      | true -> SolutionsCons (_qs_120, SolutionsNil)
      | false ->
          let rec _tr_choose_216 _x_104 =
            match _x_104 with
            | RowsEmpty -> SolutionsNil
            | RowsCons (_x_114, _xs'_113) ->
                let _l_199 (_y_115 : bool) =
                  match _y_115 with
                  | true ->
                      _tr_place_214
                        ( _op_3 (* + *) _x_119 1,
                          SolutionPlace (Queen (_x_119, _x_114), _qs_120) )
                  | false -> _tr_choose_216 _xs'_113
                in
                _op_7 (* @ *) (_l_199 true) (_l_199 false)
          in
          _tr_choose_216 (_available_68 _number_of_queens_117 _x_119 _qs_120)
    in
    _tr_place_214 (1, SolutionEmpty)
  in
  _queens_203 _number_of_queens_189

let queens_all = _queens_all_188

let _queens_one_cps_238 (_number_of_queens_239 : int) =
  let _absurd_240 (_void_241 : empty) =
    match _void_241 with _ -> assert false
  in
  (let rec _queens_265 _number_of_queens_117 =
     let rec _tr_place_118 _x_129 =
       let _x_119, _qs_120 = _x_129 in
       match _op_21 (* > *) _x_119 _number_of_queens_117 with
       | true -> Value _qs_120
       | false ->
           _tr_choose_94 (_available_68 _number_of_queens_117 _x_119 _qs_120)
           >> fun _y_123 ->
           _tr_place_118
             ( _op_3 (* + *) _x_119 1,
               SolutionPlace (Queen (_x_119, _y_123), _qs_120) )
     in
     let rec _tr_place_276 _x_129 =
       let _x_119, _qs_120 = _x_129 in
       match _op_21 (* > *) _x_119 _number_of_queens_117 with
       | true ->
           coer_arrow coer_refl_ty (coer_return coer_refl_ty)
             (fun (_ : unit -> solution computation) -> _qs_120)
       | false ->
           let rec _tr_choose_278 _x_104 =
             match _x_104 with
             | RowsEmpty ->
                 fun (_kf_248 : unit -> solution computation) -> _kf_248 ()
             | RowsCons (_x_114, _xs'_113) ->
                 let _l_254 (_y_115 : bool) =
                   match _y_115 with
                   | true ->
                       _tr_place_276
                         ( _op_3 (* + *) _x_119 1,
                           SolutionPlace (Queen (_x_119, _x_114), _qs_120) )
                   | false -> _tr_choose_278 _xs'_113
                 in
                 fun (_kf_244 : unit -> solution computation) ->
                   _l_254 true (fun (_ : unit) -> _l_254 false _kf_244)
           in
           _tr_choose_278 (_available_68 _number_of_queens_117 _x_119 _qs_120)
     in
     _tr_place_276 (1, SolutionEmpty)
   in
   _queens_265 _number_of_queens_239) (fun (() : unit) ->
      Call (Fail, (), fun (_y_264 : empty) -> Value (_absurd_240 _y_264)))

let queens_one_cps = _queens_one_cps_238
