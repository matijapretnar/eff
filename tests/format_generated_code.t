  $ for f in codegen/*.eff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "----------------------------------------------------------------------"
  >   ../eff.exe --no-stdlib --compile-plain-ocaml --no-header $f > $f.ml
  >   ocamlformat $f.ml
  > done
  ======================================================================
  codegen/application_red.eff
  ----------------------------------------------------------------------
  ;;
  3 * 2
  ======================================================================
  codegen/break-split.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two_42 = 2
  
  let two = _two_42
  
  let _three_43 = 3
  
  let three = _three_43
  
  ;;
  let rec _f_62 _x_57 =
    let _l_54 (_y_59 : bool) = if _y_59 then 2 else 3 in
    _l_54 true + _l_54 false
  in
  _f_62 ()
  ======================================================================
  codegen/constant_folding_match.eff
  ----------------------------------------------------------------------
  type a = Nil | Cons of (int * a)
  
  let _f_42 (_x_43 : int) = match _x_43 with 1 -> 0 | _ -> 4
  
  let f = _f_42
  
  let _g_44 (_a_45 : a) =
    ( (match _a_45 with
      | Nil -> 0
      | Cons (_x_47, Nil) -> _x_47 + 4
      | Cons (4, _x_49) -> 7
      | _x_50 -> 13),
      0,
      3 + 4,
      13,
      7 )
  
  let g = _g_44
  ======================================================================
  codegen/handle_match.eff
  ----------------------------------------------------------------------
  type int_list = Nil | Cons of (int * int_list)
  
  let _f_42 (_y_43 : int_list) =
    match _y_43 with
    | Nil -> 1 + 10
    | Cons (_x_48, Nil) -> _x_48 + 10
    | Cons (_, Cons (_y_49, Nil)) -> _y_49 + 10
    | Cons (_x_50, _) -> _x_50 + 10
  
  let f = _f_42
  
  ;;
  4 + 10
  ======================================================================
  codegen/handle_rec.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Eff : (unit, unit) eff_internal_effect
  
  ;;
  let rec _f_65 _x_55 = if _x_55 = 0 then 1 else _f_65 (_x_55 - 1) * 2 in
  _f_65 5
  
  ;;
  let rec _g_70 _x_81 = if _x_81 = 0 then 1 else _g_70 (_x_81 - 1) in
  _g_70 5
  ======================================================================
  codegen/handler_beta_reduction.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Eff : (int, int) eff_internal_effect
  
  ;;
  1 + 3 + 2 + 4
  ======================================================================
  codegen/ifthenelse.eff
  ----------------------------------------------------------------------
  ;;
  ()
  ======================================================================
  codegen/is_relatively_pure.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op1 : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (int, unit) eff_internal_effect
  
  ;;
  Call (Op1, 1, fun (_y_51 : unit) -> Value _y_51)
  ======================================================================
  codegen/let_list_to_bind.eff
  ----------------------------------------------------------------------
  ;;
  2 + 1
  ======================================================================
  codegen/match_red.eff
  ----------------------------------------------------------------------
  ;;
  1
  ======================================================================
  codegen/nested_handlers.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Fail : (unit, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _test_nested_42 (_m_43 : int) =
    let rec _simple_65 _x_55 = _m_43 in
    _simple_65 ()
  
  let test_nested = _test_nested_42
  
  let _test_nested_69 (_m_70 : int) =
    let rec _go_111 _x_90 =
      if _x_90 = 0 then Call (Fail, (), fun (_y_105 : unit) -> Value _y_105)
      else
        let _l_92 (_y_106 : bool) =
          if _y_106 then _go_111 (_x_90 - 1) else _go_111 (_x_90 - 2)
        in
        (handler
           {
             value_clause = (fun (_id_82 : unit) -> Value _id_82);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Fail -> fun () _l_91 -> _l_92 false
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_l_92 true)
    in
    _go_111 _m_70
  
  let test_nested = _test_nested_69
  ======================================================================
  codegen/norec.eff
  ----------------------------------------------------------------------
  let _f_42 (_x_43 : float) = ()
  
  let f = _f_42
  ======================================================================
  codegen/not-found.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  
  ;;
  11
  ======================================================================
  codegen/one_input.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  ;;
  let _l_53 (_y_64 : bool) = if _y_64 then 10 else 20 in
  _l_53 true + _l_53 false
  ======================================================================
  codegen/optimize_pattern_match.eff
  ----------------------------------------------------------------------
  let _k_42 (_b_43 : int) =
    let rec _a_44 (_x_45, _y_46) (_z_47 : int) = _x_45 + _y_46 + _z_47 + _b_43 in
    _a_44
  
  let k = _k_42
  ======================================================================
  codegen/optimize_short_circuit.eff
  ----------------------------------------------------------------------
  let _a_42 (_b_43 : bool) (_c_44 : bool) = _b_43 && _c_44
  
  let a = _a_42
  ======================================================================
  codegen/original.eff
  ----------------------------------------------------------------------
  ;;
  let rec _loop_42 _x_48 = if _x_48 = 0 then 0 else _loop_42 (_x_48 - 1) in
  _loop_42 10
  ======================================================================
  codegen/other-effect.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += WriteInt : (int, unit) eff_internal_effect
  
  ;;
  let rec _f_67 _x_58 = _x_58 + if _x_58 = 0 then 0 else _f_67 (_x_58 - 1) in
  _f_67 10
  ======================================================================
  codegen/pm-1_fails.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two_42 = 2
  
  let two = _two_42
  
  let _three_43 = 3
  
  let three = _three_43
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  force_unsafe
    ((let rec _concat_45 _x_63 (_x_0 : intlist) =
        match _x_63 with
        | IntNil -> _x_0
        | IntCons (_z_75, _zs_74) -> IntCons (_z_75, _concat_45 _zs_74 _x_0)
      in
      handler
        {
          value_clause = (fun (_x_57 : int) -> Value (IntCons (_x_57, IntNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun () _l_64 ->
                    Value
                      (_concat_45
                         (coer_arrow coer_refl_ty force_unsafe _l_64 true)
                         (coer_arrow coer_refl_ty force_unsafe _l_64 false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (let rec _f_60 _x_67 =
          Call (Decide, (), fun (_y_69 : bool) -> Value (if _y_69 then 2 else 3))
        in
        _f_60 ()))
  ======================================================================
  codegen/pm-2_passes.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two_42 = 2
  
  let two = _two_42
  
  let _three_43 = 3
  
  let three = _three_43
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  let rec _concat_44 _x_62 (_x_0 : intlist) =
    match _x_62 with
    | IntNil -> _x_0
    | IntCons (_z_75, _zs_74) -> IntCons (_z_75, _concat_44 _zs_74 _x_0)
  in
  let rec _f_71 _x_66 =
    let _l_63 (_y_68 : bool) = IntCons ((if _y_68 then 2 else 3), IntNil) in
    _concat_44 (_l_63 true) (_l_63 false)
  in
  _f_71 ()
  ======================================================================
  codegen/pm-3_passes.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  let rec _concat_42 _x_62 (_x_0 : intlist) =
    match _x_62 with
    | IntNil -> _x_0
    | IntCons (_z_78, _zs_77) -> IntCons (_z_78, _concat_42 _zs_77 _x_0)
  in
  let _l_63 (_y_72 : bool) =
    let _l_63 (_y_69 : bool) =
      IntCons (((if _y_72 then 10 else 20) - if _y_69 then 0 else 5), IntNil)
    in
    _concat_42 (_l_63 true) (_l_63 false)
  in
  _concat_42 (_l_63 true) (_l_63 false)
  ======================================================================
  codegen/rec1.eff
  ----------------------------------------------------------------------
  ;;
  let rec _f_42 _x_44 = () in
  _f_42 1
  ======================================================================
  codegen/rec2.eff
  ----------------------------------------------------------------------
  ;;
  10
  ======================================================================
  codegen/redefine_local.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Ping : (unit, unit) eff_internal_effect
  
  let _test_simple_42 (_x_43 : float) = ((), 1)
  
  let test_simple = _test_simple_42
  
  let _test_simple2_60 (() : unit) = ()
  
  let test_simple2 = _test_simple2_60
  ======================================================================
  codegen/substitution.eff
  ----------------------------------------------------------------------
  let _decide_func_42 (_bl_43 : bool) = if _bl_43 then 10 else 20
  
  let decide_func = _decide_func_42
  ======================================================================
  codegen/test-handle_effect_skip.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  ;;
  Call (Print, "hello\n", fun (_y_47 : unit) -> Value (match _y_47 with _ -> 42))
  ======================================================================
  codegen/test1.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test10.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test11.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect
  ======================================================================
  codegen/test12.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect
  
  ;;
  coer_hand_to_fun coer_refl_ty force_unsafe
    (handler
       {
         value_clause = (fun (_x_46 : int) -> Value _x_46);
         effect_clauses =
           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                (a -> (b -> _) -> _) ->
             match eff with
             | Op1 -> fun _n_42 _l_49 -> Value 1
             | Op2 -> fun _n_44 _l_50 -> Value 2
             | eff' -> fun arg k -> Call (eff', arg, k));
       })
  ======================================================================
  codegen/test13.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect
  
  ;;
  1
  ======================================================================
  codegen/test14.eff
  ----------------------------------------------------------------------
  type integer = int
  
  type (_, _) eff_internal_effect += Op : (unit, int) eff_internal_effect
  
  ;;
  fun (_y_43 : int) -> Call (Op, (), fun (_y_49 : int) -> Value (_y_49 + _y_43))
  ======================================================================
  codegen/test15.eff
  ----------------------------------------------------------------------
  type foo = A | B of bar
  
  and bar = { x : foo }
  
  type (_, _) eff_internal_effect += Op1 : (int, bar) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (bar, foo) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op3 : (foo, int) eff_internal_effect
  
  ;;
  fun (_a_43 : int) ->
    Call
      ( Op1,
        10,
        fun (_y_64 : bar) ->
          Call
            ( Op2,
              _y_64,
              fun (_y_66 : foo) ->
                Call (Op3, _y_66, fun (_y_67 : int) -> Value (_a_43 + _y_67)) ) )
  ======================================================================
  codegen/test16.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect
  
  ;;
  let rec _loop_85 _x_66 (_x_0 : int) =
    if 0 < _x_66 then _loop_85 (_x_66 - 1) (_x_0 + 1) else ()
  in
  _loop_85 10 0
  ======================================================================
  codegen/test17.eff
  ----------------------------------------------------------------------
  type my_ty = Cons of my_ty
  
  ;;
  fun (Cons _argmnt_43 : my_ty) -> Cons _argmnt_43
  ======================================================================
  codegen/test18.eff
  ----------------------------------------------------------------------
  type nat = Zero | Succ of nat
  
  ;;
  let rec _add_42 _x_48 (_x_50 : nat) =
    match _x_50 with Zero -> _x_48 | Succ _n_51 -> Succ (_add_42 _x_48 _n_51)
  in
  _add_42
  ======================================================================
  codegen/test19.eff
  ----------------------------------------------------------------------
  type nat = Zero | Succ of nat
  
  ;;
  fun ((_w_43, _k_44, _num_45) : nat * nat * int) (_x_46 : nat * nat * int) ->
    match _x_46 with
    | Zero, Zero, 0 -> (_w_43, _k_44, Zero, 0, 0)
    | Zero, _z_47, _n_48 -> (Zero, _z_47, Zero, _num_45, _n_48)
    | _x_49, Zero, _n_50 -> (Zero, _w_43, _x_49, 1, _n_50)
    | _, _, _ -> (Zero, Zero, Zero, 0, 0)
  ======================================================================
  codegen/test2.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test20.eff
  ----------------------------------------------------------------------
  let rec _even_43 _x_55 = _x_55 = 0 || _odd_42 (_x_55 - 1)
  
  and _odd_42 _x_54 = if _x_54 = 0 then false else _even_43 (_x_54 - 1)
  
  let even, odd = (_even_43, _odd_42)
  ======================================================================
  codegen/test21.eff
  ----------------------------------------------------------------------
  ;;
  1, true
  ======================================================================
  codegen/test3.eff
  ----------------------------------------------------------------------
  ;;
  fun (_x_42 : float) -> _x_42
  ======================================================================
  codegen/test4.eff
  ----------------------------------------------------------------------
  ;;
  1
  ======================================================================
  codegen/test5.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  
  ;;
  coer_hand_to_fun coer_refl_ty force_unsafe
    (handler
       {
         value_clause = (fun (_id_44 : int) -> Value _id_44);
         effect_clauses =
           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                (a -> (b -> _) -> _) ->
             match eff with
             | Op -> fun _n_42 _l_46 -> Value 2
             | eff' -> fun arg k -> Call (eff', arg, k));
       })
  ======================================================================
  codegen/test6.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  
  ;;
  1
  ======================================================================
  codegen/test7.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  
  ;;
  2
  ======================================================================
  codegen/test8.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  
  ;;
  2
  ======================================================================
  codegen/test9.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  
  ;;
  1
  ======================================================================
  codegen/top-letrec_fails.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  let rec _concat_42 _x_50 (_x_0 : intlist) =
    match _x_50 with
    | IntNil -> _x_0
    | IntCons (_z_54, _zs_53) -> IntCons (_z_54, _concat_42 _zs_53 _x_0)
  
  let concat = _concat_42
  
  ;;
  IntNil
  ======================================================================
  codegen/two_inputs.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type int_list = Nil | Cons of (int * int_list)
  
  ;;
  let rec _op_42 (* @ *) _x_62 (_ys_81 : int_list) =
    match _x_62 with
    | Nil -> _ys_81
    | Cons (_x_83, _xs_82) -> Cons (_x_83, _op_42 (* @ *) _xs_82 _ys_81)
  in
  let _l_63 (_y_79 : bool) = Cons ((if _y_79 then 10 else 20), Nil) in
  _op_42 (* @ *) (_l_63 true) (_l_63 false)
-------------------------------------------------------------------------------
