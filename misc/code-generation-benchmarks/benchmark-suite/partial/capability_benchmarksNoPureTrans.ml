open OcamlHeader

(* Manually inserted some value casts *)

type (_, _) eff_internal_effect += TripleFlip : (unit, bool) eff_internal_effect

type (_, _) eff_internal_effect +=
  | TripleFail : (unit, empty) eff_internal_effect

type triple_int_list =
  | TripleCons of ((int * int * int) * triple_int_list)
  | TripleNil

let rec _op_42 (* @ *) _x_49 _ys_51 =
  match _x_49 with
  | TripleNil -> Value _ys_51
  | TripleCons (_x_53, _xs_52) ->
      Value (_op_42 (* @ *) _xs_52) >>= fun _b_54 ->
      Value (_b_54 _ys_51) >>= fun (Value _b_55) ->
      Value (TripleCons (_x_53, _b_55))

let _op_42 (* @ *) = _op_42 (* @ *)

let _testTriple_56 (_n_57 : int) (_s_58 : int) =
  let rec _choice_679 _x_680 =
    Value (( < ) _x_680) >>= fun _x_681 ->
    Value (_x_681 1) >>= fun _x_682 ->
    if _x_682 then Value TripleNil
    else
      let _l_683 (_y_687 : bool) =
        if _y_687 then
          Value (( - ) _x_680) >>= fun _x_688 ->
          Value (_x_688 1) >>= fun _x_689 ->
          let rec _choice_690 _x_691 =
            Value (( < ) _x_691) >>= fun _x_692 ->
            Value (_x_692 1) >>= fun _x_693 ->
            if _x_693 then Value TripleNil
            else
              let _l_694 (_y_698 : bool) =
                if _y_698 then
                  Value (( - ) _x_691) >>= fun _x_699 ->
                  Value (_x_699 1) >>= fun _x_700 ->
                  let rec _choice_701 _x_702 =
                    Value (( < ) _x_702) >>= fun _x_703 ->
                    Value (_x_703 1) >>= fun _x_704 ->
                    if _x_704 then Value TripleNil
                    else
                      let _l_705 (_y_709 : bool) =
                        if _y_709 then
                          Value (( + ) _x_680) >>= fun _x_710 ->
                          Value (_x_710 _x_691) >>= fun _x_711 ->
                          Value (( + ) _x_711) >>= fun _x_712 ->
                          Value (_x_712 _x_702) >>= fun _x_713 ->
                          Value (( = ) _x_713) >>= fun _x_714 ->
                          Value (_x_714 _s_58) >>= fun _x_715 ->
                          if _x_715 then
                            Value
                              (TripleCons ((_x_680, _x_691, _x_702), TripleNil))
                          else Value TripleNil
                        else
                          Value (( - ) _x_702) >>= fun _x_716 ->
                          Value (_x_716 1) >>= fun _x_717 -> _choice_701 _x_717
                      in
                      Value (_l_705 true) >>= fun _xs_706 ->
                      Value (_l_705 false) >>= fun _ys_707 ->
                      Value (_op_42 (* @ *) (force_unsafe _xs_706))
                      >>= fun _b_708 -> _b_708 (force_unsafe _ys_707)
                  in
                  _choice_701 _x_700
                else
                  Value (( - ) _x_691) >>= fun _x_718 ->
                  Value (_x_718 1) >>= fun _x_719 -> _choice_690 _x_719
              in
              Value (_l_694 true) >>= fun _xs_695 ->
              Value (_l_694 false) >>= fun _ys_696 ->
              Value (_op_42 (* @ *) (force_unsafe _xs_695)) >>= fun _b_697 ->
              _b_697 (force_unsafe _ys_696)
          in
          _choice_690 _x_689
        else
          Value (( - ) _x_680) >>= fun _x_720 ->
          Value (_x_720 1) >>= fun _x_721 -> _choice_679 _x_721
      in
      Value (_l_683 true) >>= fun (Value _xs_684) ->
      Value (_l_683 false) >>= fun (Value _ys_685) ->
      Value (_op_42 (* @ *) _xs_684) >>= fun _b_686 -> _b_686 _ys_685
  in
  _choice_679 _n_57

let testTriple = _testTriple_56

let _handleTripleWrap_723 ((_x_724, _y_725) : int * int) =
  Value (_testTriple_56 _x_724) >>= fun _b_726 -> _b_726 _y_725

let handleTripleWrap = _handleTripleWrap_723

type queen = int * int

type queen_list = Nil | Cons of (queen * queen_list)

type queen_list_list = QNil | QCons of (queen_list * queen_list_list)

type intlist = End | Lst of (int * intlist)

type option = Some of queen_list | None

type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect

let rec _filter_727 _x_736 _x_738 =
  match _x_738 with
  | End -> Value End
  | Lst (_x_740, _xs_739) ->
      Value (_x_736 _x_740) >>= fun _b_741 ->
      if _b_741 then
        Value (_filter_727 _x_736) >>= fun _b_742 ->
        Value (_b_742 _xs_739) >>= fun _b_743 ->
        Value (Lst (_x_740, force_unsafe _b_743))
      else Value (_filter_727 _x_736) >>= fun _b_744 -> _b_744 _xs_739

let filter = _filter_727

let rec _forall_745 _x_752 (_x_754 : queen_list) =
  match _x_754 with
  | Nil -> Value true
  | Cons (_x_756, _xs_755) ->
      Value (_x_752 _x_756) >>= fun _b_757 ->
      Value (_b_757 && force_unsafe (_forall_745 _x_752 _xs_755))

let forall = _forall_745

let _no_attack_759 ((_x_760, _y_761) : int * int)
    ((_x'_762, _y'_763) : int * int) =
  Value (( <> ) _x_760) >>= fun _b_765 ->
  Value (_b_765 _x'_762) >>= fun _b_764 ->
  Value
    (_b_764
    && force_unsafe
         ( Value (( <> ) _y_761) >>= fun _b_767 ->
           Value (_b_767 _y'_763) >>= fun _b_766 -> Value _b_766 )
    && force_unsafe
         ( Value (( - ) _x_760) >>= fun _b_771 ->
           Value (_b_771 _x'_762) >>= fun _b_770 ->
           Value (abs _b_770) >>= fun _b_769 ->
           Value (( <> ) _b_769) >>= fun _b_768 ->
           Value (( - ) _y_761) >>= fun _b_774 ->
           Value (_b_774 _y'_763) >>= fun _b_773 ->
           Value (abs _b_773) >>= fun _b_772 -> Value (_b_768 _b_772) ))

let no_attack = _no_attack_759

let _available_775 (_x_776 : int) (_qs_777 : queen_list) (_l_778 : intlist) :
    intlist computation =
  Value
    (_filter_727 (fun (_y_780 : int) ->
         force_unsafe
           ( Value (_no_attack_759 (_x_776, _y_780)) >>= fun _b_782 ->
             Value (_forall_745 (fun x -> force_unsafe (_b_782 x)))
             >>= fun _b_781 -> _b_781 _qs_777 )))
  >>= fun _b_779 -> _b_779 _l_778

let available = _available_775

let _find_solution_783 (_n_784 : int) =
  let rec _init_798 _x_823 (_acc_845 : intlist) =
    Value (( = ) _x_823) >>= fun _b_846 ->
    Value (_b_846 0) >>= fun _b_847 ->
    if _b_847 then Value _acc_845
    else
      Value (( - ) _x_823) >>= fun _b_848 ->
      Value (_b_848 1) >>= fun _b_849 ->
      Value (_init_798 _b_849) >>= fun _b_850 -> _b_850 (Lst (_x_823, _acc_845))
  in
  Value (_init_798 _n_784) >>= fun _x_1011 ->
  Value (_x_1011 End) >>= fun _x_1049 ->
  let rec _place_1063 (_x_1065, _qs_1064) =
    Value (( = ) _x_1065) >>= fun _x_1066 ->
    Value (( + ) _n_784) >>= fun _x_1067 ->
    Value (_x_1067 1) >>= fun _x_1068 ->
    Value (_x_1066 _x_1068) >>= fun _x_1069 ->
    if _x_1069 then Value (Some _qs_1064)
    else
      Value (_available_775 _x_1065) >>= fun _x_1070 ->
      Value (_x_1070 _qs_1064) >>= fun _x_1071 ->
      Value (_x_1071 (force_unsafe _x_1049)) >>= fun _x_1072 ->
      let rec _loop_1073 _x_1074 (_x_1075 : intlist) : option computation =
        match _x_1075 with
        | End -> Value None
        | Lst (_x_1077, _xs_1076) -> (
            Value (_x_1074 _x_1077) >>= fun _b_1078 ->
            match _b_1078 with
            | None ->
                Value (_loop_1073 _x_1074) >>= fun _b_1079 -> _b_1079 _xs_1076
            | Some _x_1080 -> Value (Some _x_1080))
      in
      Value
        (_loop_1073 (fun (_y_1082 : int) ->
             force_unsafe
               ( Value (( + ) _x_1065) >>= fun _x_1083 ->
                 Value (_x_1083 1) >>= fun _x_1084 ->
                 _place_1063 (_x_1084, Cons ((_x_1065, _y_1082), _qs_1064)) )))
      >>= fun _b_1081 -> _b_1081 (force_unsafe _x_1072)
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
        Value (( = ) _y_1101) >>= fun _b_1090 ->
        Value (_b_1090 0) >>= fun _b_1089 ->
        if _b_1089 then Value _y_1101
        else
          Value (( - ) _y_1101) >>= fun _b_1092 ->
          Value (_b_1092 1) >>= fun _b_1091 ->
          Call (CountPut, _b_1091, fun (_y_1099 : unit) -> _count_1087 ()) )

let count = _count_1087

let _testCount_1102 (_m_1103 : int) : int computation = Value 1

(* Value
     (let rec _count_1120 _x_1097 (_s_1164 : int) =
        Value (( = ) _s_1164) >>= fun _x_1167 ->
        Value (_x_1167 0) >>= fun _x_1168 ->
        Value
          (if _x_1168 then fun (_x_1169 : int) -> _x_1169
          else
            Value (( - ) _s_1164) >>= fun _x_1170 ->
            Value (_x_1170 1) >>= fun _x_1171 (_ : int) ->
            Value (_count_1120 ()) >>= fun _b_1172 -> _b_1172 _x_1171)
        >>= fun _b_1165 -> _b_1165 _s_1164
      in
      _count_1120 ())
   >>= fun _b_1119 -> _b_1119 _m_1103 *)

let testCount x = force_unsafe (_testCount_1102 x)

type (_, _) eff_internal_effect +=
  | GeneratorPut : (int, unit) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorGet : (unit, int) eff_internal_effect

type (_, _) eff_internal_effect +=
  | GeneratorYield : (int, unit) eff_internal_effect

let _testGenerator_1173 (_n_1174 : int) : int computation =
  Value
    (let rec _generateFromTo_1266 (_l_1176, _u_1177) =
       Value (( > ) _l_1176) >>= fun _x_1322 ->
       Value (_x_1322 _u_1177) >>= fun _x_1332 ->
       if _x_1332 then Value (fun (_s_1333 : int) -> Value _s_1333)
       else
         Value
           (fun (_s_1334 : int) ->
             Value (( + ) _s_1334) >>= fun _x_1335 ->
             Value (_x_1335 _l_1176) >>= fun _x_1336 ->
             Value (( + ) _l_1176) >>= fun _x_1337 ->
             Value (_x_1337 1) >>= fun _x_1338 ->
             Value (_generateFromTo_1266 (_x_1338, _u_1177)) >>= fun _b_1339 ->
             (force_unsafe _b_1339) _x_1336)
     in
     _generateFromTo_1266 (1, _n_1174))
  >>= fun _b_1182 -> (force_unsafe _b_1182) 0

let testGenerator = _testGenerator_1173
