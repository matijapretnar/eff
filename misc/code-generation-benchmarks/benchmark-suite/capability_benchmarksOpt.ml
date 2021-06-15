open OcamlHeader

type (_, _) eff_internal_effect += TripleFlip : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect +=
  | TripleFail : (unit, empty) eff_internal_effect

type triple_int_list =
  | TripleCons of ((int * int * int) * triple_int_list)
  | TripleNil

let rec _op_42 (* @ *) _x_49 (_ys_51 : triple_int_list) =
  match _x_49 with
  | TripleNil -> _ys_51
  | TripleCons (_x_53, _xs_52) ->
      TripleCons (_x_53, _op_42 (* @ *) _xs_52 _ys_51)

let _op_42 (* @ *) = _op_42 (* @ *)

let _testTriple_56 (_n_57 : int) (_s_58 : int) =
  let rec _choice_649 _x_650 =
    if _x_650 < 1 then TripleNil
    else
      let _l_653 (_y_657 : bool) =
        if _y_657 then
          let rec _choice_660 _x_661 =
            if _x_661 < 1 then TripleNil
            else
              let _l_664 (_y_668 : bool) =
                if _y_668 then
                  let rec _choice_671 _x_672 =
                    if _x_672 < 1 then TripleNil
                    else
                      let _l_675 (_y_679 : bool) =
                        if _y_679 then
                          if _x_650 + _x_661 + _x_672 = _s_58 then
                            TripleCons ((_x_650, _x_661, _x_672), TripleNil)
                          else TripleNil
                        else _choice_671 (_x_672 - 1)
                      in
                      _op_42 (* @ *) (_l_675 true) (_l_675 false)
                  in
                  _choice_671 (_x_661 - 1)
                else _choice_660 (_x_661 - 1)
              in
              _op_42 (* @ *) (_l_664 true) (_l_664 false)
          in
          _choice_660 (_x_650 - 1)
        else _choice_649 (_x_650 - 1)
      in
      _op_42 (* @ *) (_l_653 true) (_l_653 false)
  in
  _choice_649 _n_57

let testTriple = _testTriple_56

let _handleTripleWrap_693 ((_x_694, _y_695) : int * int) =
  _testTriple_56 _x_694 _y_695

let handleTripleWrap = _handleTripleWrap_693

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_697 _x_706 (_x_708 : intlist) =
  match _x_708 with
  | End -> End
  | Lst (_x_710, _xs_709) ->
      if _x_706 _x_710 then Lst (_x_710, _filter_697 _x_706 _xs_709)
      else _filter_697 _x_706 _xs_709

let filter = _filter_697

let rec _forall_715 _x_722 (_x_724 : queen_list) =
  match _x_724 with
  | Nil -> true
  | Cons (_x_726, _xs_725) -> _x_722 _x_726 && _forall_715 _x_722 _xs_725

let forall = _forall_715

let _no_attack_729 ((_x_730, _y_731) : int * int)
    ((_x'_732, _y'_733) : int * int) =
  _x_730 <> _x'_732 && _y_731 <> _y'_733
  && abs (_x_730 - _x'_732) <> abs (_y_731 - _y'_733)

let no_attack = _no_attack_729

let _available_745 (_x_746 : int) (_qs_747 : queen_list) (_l_748 : intlist) =
  _filter_697
    (fun (_y_750 : int) ->
      _forall_715 (_no_attack_729 (_x_746, _y_750)) _qs_747)
    _l_748

let available = _available_745

let _find_solution_753 (_n_754 : int) =
  let rec _init_768 _x_793 (_acc_815 : intlist) =
    if _x_793 = 0 then _acc_815
    else _init_768 (_x_793 - 1) (Lst (_x_793, _acc_815))
  in
  let rec _place_1033 (_x_1035, _qs_1034) =
    if _x_1035 = _n_754 + 1 then Some _qs_1034
    else
      let rec _loop_1043 _x_1044 (_x_1045 : intlist) =
        match _x_1045 with
        | End -> None
        | Lst (_x_1047, _xs_1046) -> (
            match _x_1044 _x_1047 with
            | None -> _loop_1043 _x_1044 _xs_1046
            | Some _x_1050 -> Some _x_1050)
      in
      _loop_1043
        (fun (_y_1052 : int) ->
          _place_1033 (_x_1035 + 1, Cons ((_x_1035, _y_1052), _qs_1034)))
        (_available_745 _x_1035 _qs_1034 (_init_768 _n_754 End))
  in
  _place_1033 (1, Nil)

let find_solution = _find_solution_753

let _queens_all_1055 (_number_of_queens_1056 : int) =
  _find_solution_753 _number_of_queens_1056

let queens_all = _queens_all_1055

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_1057 _x_1067 =
  Call
    ( CountGet,
      (),
      fun (_y_1071 : int) ->
        if _y_1071 = 0 then Value _y_1071
        else Call (CountPut, _y_1071 - 1, fun (_y_1069 : unit) -> _count_1057 ())
    )

let count = _count_1057

let _testCount_1072 (_m_1073 : int) =
  let rec _count_1090 _x_1067 (_s_1134 : int) =
    if _s_1134 = 0 then _s_1134 else _count_1090 () (_s_1134 - 1)
  in
  _count_1090 () _m_1073

let testCount = _testCount_1072

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_1143 (_n_1144 : int) =
  let rec _generateFromTo_1234 (_l_1146, _u_1147) (_x_1 : int) =
    if _l_1146 > _u_1147 then _x_1
    else _generateFromTo_1234 (_l_1146 + 1, _u_1147) (_x_1 + _l_1146)
  in
  _generateFromTo_1234 (1, _n_1144) 0

let testGenerator = _testGenerator_1143
