open OcamlHeader

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_42 _x_51 (_x_53 : intlist) =
  match _x_53 with
  | End -> End
  | Lst (_x_55, _xs_54) ->
      if _x_51 _x_55 then Lst (_x_55, _filter_42 _x_51 _xs_54)
      else _filter_42 _x_51 _xs_54

let filter = _filter_42

let rec _forall_60 _x_67 (_x_69 : queen_list) =
  match _x_69 with
  | Nil -> true
  | Cons (_x_71, _xs_70) -> _x_67 _x_71 && _forall_60 _x_67 _xs_70

let forall = _forall_60

let _no_attack_74 ((_x_75, _y_76) : int * int) ((_x'_77, _y'_78) : int * int) =
  _x_75 <> _x'_77 && _y_76 <> _y'_78
  && abs (_x_75 - _x'_77) <> abs (_y_76 - _y'_78)

let no_attack = _no_attack_74

let _available_90 (_x_91 : int) (_qs_92 : queen_list) (_l_93 : intlist) =
  _filter_42
    (fun (_y_95 : int) -> _forall_60 (_no_attack_74 (_x_91, _y_95)) _qs_92)
    _l_93

let available = _available_90

let _find_solution_98 (_n_99 : int) =
  let rec _init_113 _x_140 (_acc_164 : intlist) =
    if _x_140 = 0 then _acc_164
    else _init_113 (_x_140 - 1) (Lst (_x_140, _acc_164))
  in
  let rec _place_123 _x_143 (_qs_151 : queen_list) =
    if _x_143 = _n_99 + 1 then Value (Some _qs_151)
    else
      Call
        ( Select,
          _available_90 _x_143 _qs_151 (_init_113 _n_99 End),
          fun (_y_159 : int) ->
            _place_123 (_x_143 + 1) (Cons ((_x_143, _y_159), _qs_151)) )
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id_111 : option) -> Value _id_111);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Select ->
                  fun _lst_100 _l_139 ->
                    Value
                      (let rec _loop_102 _x_138 (_x_171 : intlist) =
                         match _x_171 with
                         | End -> None
                         | Lst (_x_173, _xs_172) -> (
                             match _x_138 _x_173 with
                             | None -> _loop_102 _x_138 _xs_172
                             | Some _x_176 -> Some _x_176)
                       in
                       _loop_102
                         (coer_arrow coer_refl_ty force_unsafe _l_139)
                         _lst_100)
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (_place_123 1 Nil))

let find_solution = _find_solution_98

let _queens_all_177 (_number_of_queens_178 : int) =
  _find_solution_98 _number_of_queens_178

let queens_all = _queens_all_177

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_179 _x_189 =
  Call
    ( CountGet,
      (),
      fun (_y_193 : int) ->
        if _y_193 = 0 then Value _y_193
        else Call (CountPut, _y_193 - 1, fun (_y_191 : unit) -> _count_179 ())
    )

let count = _count_179

let _testCount_194 (_m_195 : int) =
  (let rec _count_212 _x_189 (_s_225 : int) =
     (if _s_225 = 0 then fun (_ : int) -> _s_225
     else fun (_ : int) -> _count_212 () (_s_225 - 1))
       _s_225
   in
   _count_212 ())
    _m_195

let testCount = _testCount_194

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorProduce : (int, int) eff_internal_effect

let _testGenerator_233 (_m_234 : int) =
  let rec _sum_350 _x_351 =
    if _x_351 = 0 then
      Call (GeneratorGet, (), fun (_y_354 : int) -> Value _y_354)
    else
      Call
        ( GeneratorGet,
          (),
          fun (_y_355 : int) ->
            Call
              ( GeneratorProduce,
                _x_351,
                fun (_y_357 : int) ->
                  Call
                    ( GeneratorPut,
                      _y_355 + _y_357,
                      fun (_y_359 : unit) -> _sum_350 (_x_351 - 1) ) ) )
  in
  (let rec _sum_363 _x_364 =
     if _x_364 = 0 then
       Call (GeneratorGet, (), fun (_y_367 : int) -> Value _y_367)
     else
       Call
         ( GeneratorGet,
           (),
           fun (_y_368 : int) ->
             Call
               ( GeneratorPut,
                 _y_368 + (_x_364 mod 42),
                 fun (_y_373 : unit) -> _sum_363 (_x_364 - 1) ) )
   in
   let rec _sum_376 _x_377 =
     if _x_377 = 0 then fun (_s_380 : int) -> _s_380
     else fun (_s_381 : int) -> _sum_376 (_x_377 - 1) (_s_381 + (_x_377 mod 42))
   in
   _sum_376 _m_234)
    _m_234

let testGenerator = _testGenerator_233
