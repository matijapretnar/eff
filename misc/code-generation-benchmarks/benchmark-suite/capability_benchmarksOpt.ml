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
  let rec _choice_679 _x_680 =
    if _x_680 < 1 then TripleNil
    else
      let _l_683 (_y_687 : bool) =
        if _y_687 then
          let rec _choice_690 _x_691 =
            if _x_691 < 1 then TripleNil
            else
              let _l_694 (_y_698 : bool) =
                if _y_698 then
                  let rec _choice_701 _x_702 =
                    if _x_702 < 1 then TripleNil
                    else
                      let _l_705 (_y_709 : bool) =
                        if _y_709 then
                          if _x_680 + _x_691 + _x_702 = _s_58 then
                            TripleCons ((_x_680, _x_691, _x_702), TripleNil)
                          else TripleNil
                        else _choice_701 (_x_702 - 1)
                      in
                      _op_42 (* @ *) (_l_705 true) (_l_705 false)
                  in
                  _choice_701 (_x_691 - 1)
                else _choice_690 (_x_691 - 1)
              in
              _op_42 (* @ *) (_l_694 true) (_l_694 false)
          in
          _choice_690 (_x_680 - 1)
        else _choice_679 (_x_680 - 1)
      in
      _op_42 (* @ *) (_l_683 true) (_l_683 false)
  in
  _choice_679 _n_57

let testTriple = _testTriple_56

let _handleTripleWrap_723 ((_x_724, _y_725) : int * int) =
  _testTriple_56 _x_724 _y_725

let handleTripleWrap = _handleTripleWrap_723

type queen = int * int
type queen_list = Nil | Cons of (queen * queen_list)
type queen_list_list = QNil | QCons of (queen_list * queen_list_list)
type intlist = End | Lst of (int * intlist)
type option = Some of queen_list | None
type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_727 _x_736 (_x_738 : intlist) =
  match _x_738 with
  | End -> End
  | Lst (_x_740, _xs_739) ->
      if _x_736 _x_740 then Lst (_x_740, _filter_727 _x_736 _xs_739)
      else _filter_727 _x_736 _xs_739

let filter = _filter_727

let rec _forall_745 _x_752 (_x_754 : queen_list) =
  match _x_754 with
  | Nil -> true
  | Cons (_x_756, _xs_755) -> _x_752 _x_756 && _forall_745 _x_752 _xs_755

let forall = _forall_745

let _no_attack_759 ((_x_760, _y_761) : int * int)
    ((_x'_762, _y'_763) : int * int) =
  _x_760 <> _x'_762 && _y_761 <> _y'_763
  && abs (_x_760 - _x'_762) <> abs (_y_761 - _y'_763)

let no_attack = _no_attack_759

let _available_775 (_x_776 : int) (_qs_777 : queen_list) (_l_778 : intlist) =
  _filter_727
    (fun (_y_780 : int) ->
      _forall_745 (_no_attack_759 (_x_776, _y_780)) _qs_777)
    _l_778

let available = _available_775

let _find_solution_783 (_n_784 : int) =
  let rec _init_798 _x_823 (_acc_845 : intlist) =
    if _x_823 = 0 then _acc_845
    else _init_798 (_x_823 - 1) (Lst (_x_823, _acc_845))
  in
  let rec _place_1063 (_x_1065, _qs_1064) =
    if _x_1065 = _n_784 + 1 then Some _qs_1064
    else
      let rec _loop_1073 _x_1074 (_x_1075 : intlist) =
        match _x_1075 with
        | End -> None
        | Lst (_x_1077, _xs_1076) -> (
            match _x_1074 _x_1077 with
            | None -> _loop_1073 _x_1074 _xs_1076
            | Some _x_1080 -> Some _x_1080)
      in
      _loop_1073
        (fun (_y_1082 : int) ->
          _place_1063 (_x_1065 + 1, Cons ((_x_1065, _y_1082), _qs_1064)))
        (_available_775 _x_1065 _qs_1064 (_init_798 _n_784 End))
  in
  _place_1063 (1, Nil)

let find_solution = _find_solution_783

let _queens_all_1085 (_number_of_queens_1086 : int) =
  _find_solution_783 _number_of_queens_1086

let queens_all = _queens_all_1085

type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect
type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect

let rec _count_1087 _x_1097 =
  Call
    ( CountGet,
      (),
      fun (_y_1101 : int) ->
        if _y_1101 = 0 then Value _y_1101
        else Call (CountPut, _y_1101 - 1, fun (_y_1099 : unit) -> _count_1087 ())
    )

let count = _count_1087

let _testCount_1102 (_m_1103 : int) =
  let rec _count_1120 _x_1097 (_s_1164 : int) =
    if _s_1164 = 0 then _s_1164 else _count_1120 () (_s_1164 - 1)
  in
  _count_1120 () _m_1103

let testCount = _testCount_1102

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_1173 (_n_1174 : int) =
  let rec _generateFromTo_1266 (_l_1176, _u_1177) (_x_1 : int) =
    if _l_1176 > _u_1177 then _x_1
    else _generateFromTo_1266 (_l_1176 + 1, _u_1177) (_x_1 + _l_1176)
  in
  _generateFromTo_1266 (1, _n_1174) 0

let testGenerator = _testGenerator_1173
