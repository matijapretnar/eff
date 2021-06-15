  $ for f in codegen/*.eff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "----------------------------------------------------------------------"
  >   ../eff.exe --no-stdlib --compile-plain-ocaml --no-header $f | sed -E 's/_[0-9]+//g' > $f.ml
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
  
  let _two = 2
  
  let two = _two
  
  let _three = 3
  
  let three = _three
  
  ;;
  let rec _f _x =
    let _l (_y : bool) = if _y then 2 else 3 in
    _l true + _l false
  in
  _f ()
  ======================================================================
  codegen/constant_folding_match.eff
  ----------------------------------------------------------------------
  type a = Nil | Cons of (int * a)
  
  let _f (_x : int) = match _x with 1 -> 0 | _ -> 4
  
  let f = _f
  
  let _g (_a : a) =
    ( (match _a with
      | Nil -> 0
      | Cons (_x, Nil) -> _x + 4
      | Cons (4, _x) -> 7
      | _x -> 13),
      0,
      3 + 4,
      13,
      7 )
  
  let g = _g
  ======================================================================
  codegen/handle_match.eff
  ----------------------------------------------------------------------
  type int_list = Nil | Cons of (int * int_list)
  
  let _f (_y : int_list) =
    match _y with
    | Nil -> 1 + 10
    | Cons (_x, Nil) -> _x + 10
    | Cons (_, Cons (_y, Nil)) -> _y + 10
    | Cons (_x, _) -> _x + 10
  
  let f = _f
  
  ;;
  4 + 10
  ======================================================================
  codegen/handle_rec.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Eff : (unit, unit) eff_internal_effect
  
  ;;
  let rec _f _x = if _x = 0 then 1 else _f (_x - 1) * 2 in
  _f 5
  
  ;;
  let rec _g _x = if _x = 0 then 1 else _g (_x - 1) in
  _g 5
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
  Call (Op1, 1, fun (_y : unit) -> Value _y)
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
  
  let _test_nested (_m : int) =
    let rec _simple _x = _m in
    _simple ()
  
  let test_nested = _test_nested
  
  let _test_nested (_m : int) =
    let rec _go _x =
      if _x = 0 then Call (Fail, (), fun (_y : unit) -> Value _y)
      else
        let _l (_y : bool) = if _y then _go (_x - 1) else _go (_x - 2) in
        (handler
           {
             value_clause = (fun (_id : unit) -> Value _id);
             effect_clauses =
               (fun (type a b) (eff : (a, b) eff_internal_effect) :
                    (a -> (b -> _) -> _) ->
                 match eff with
                 | Fail -> fun () _l -> _l false
                 | eff' -> fun arg k -> Call (eff', arg, k));
           })
          (_l true)
    in
    _go _m
  
  let test_nested = _test_nested
  ======================================================================
  codegen/norec.eff
  ----------------------------------------------------------------------
  let _f (_x : float) = ()
  
  let f = _f
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
  let _l (_y : bool) = if _y then 10 else 20 in
  _l true + _l false
  ======================================================================
  codegen/optimize_pattern_match.eff
  ----------------------------------------------------------------------
  let _k (_b : int) =
    let rec _a (_x, _y) (_z : int) = _x + _y + _z + _b in
    _a
  
  let k = _k
  ======================================================================
  codegen/optimize_short_circuit.eff
  ----------------------------------------------------------------------
  let _a (_b : bool) (_c : bool) = _b && _c
  
  let a = _a
  ======================================================================
  codegen/original.eff
  ----------------------------------------------------------------------
  ;;
  let rec _loop _x = if _x = 0 then 0 else _loop (_x - 1) in
  _loop 10
  ======================================================================
  codegen/other-effect.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += WriteInt : (int, unit) eff_internal_effect
  
  ;;
  let rec _f _x = _x + if _x = 0 then 0 else _f (_x - 1) in
  _f 10
  ======================================================================
  codegen/pm-1_fails.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two = 2
  
  let two = _two
  
  let _three = 3
  
  let three = _three
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  force_unsafe
    ((let rec _concat _x (_x : intlist) =
        match _x with
        | IntNil -> _x
        | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
      in
      handler
        {
          value_clause = (fun (_x : int) -> Value (IntCons (_x, IntNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun () _l ->
                    Value
                      (_concat
                         (coer_arrow coer_refl_ty force_unsafe _l true)
                         (coer_arrow coer_refl_ty force_unsafe _l false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        })
       (let rec _f _x =
          Call (Decide, (), fun (_y : bool) -> Value (if _y then 2 else 3))
        in
        _f ()))
  ======================================================================
  codegen/pm-2_passes.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two = 2
  
  let two = _two
  
  let _three = 3
  
  let three = _three
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  in
  let rec _f _x =
    let _l (_y : bool) = IntCons ((if _y then 2 else 3), IntNil) in
    _concat (_l true) (_l false)
  in
  _f ()
  ======================================================================
  codegen/pm-3_passes.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type intlist = IntNil | IntCons of (int * intlist)
  
  ;;
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  in
  let _l (_y : bool) =
    let _l (_y : bool) =
      IntCons (((if _y then 10 else 20) - if _y then 0 else 5), IntNil)
    in
    _concat (_l true) (_l false)
  in
  _concat (_l true) (_l false)
  ======================================================================
  codegen/rec1.eff
  ----------------------------------------------------------------------
  ;;
  let rec _f _x = () in
  _f 1
  ======================================================================
  codegen/rec2.eff
  ----------------------------------------------------------------------
  ;;
  10
  ======================================================================
  codegen/redefine_local.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Ping : (unit, unit) eff_internal_effect
  
  let _test_simple (_x : float) = ((), 1)
  
  let test_simple = _test_simple
  
  let _test_simple2 (() : unit) = ()
  
  let test_simple2 = _test_simple2
  ======================================================================
  codegen/substitution.eff
  ----------------------------------------------------------------------
  let _decide_func (_bl : bool) = if _bl then 10 else 20
  
  let decide_func = _decide_func
  ======================================================================
  codegen/test-handle_effect_skip.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  ;;
  Call (Print, "hello\n", fun (_y : unit) -> Value (match _y with _ -> 42))
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
         value_clause = (fun (_x : int) -> Value _x);
         effect_clauses =
           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                (a -> (b -> _) -> _) ->
             match eff with
             | Op1 -> fun _n _l -> Value 1
             | Op2 -> fun _n _l -> Value 2
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
  fun (_y : int) -> Call (Op, (), fun (_y : int) -> Value (_y + _y))
  ======================================================================
  codegen/test15.eff
  ----------------------------------------------------------------------
  type foo = A | B of bar
  
  and bar = { x : foo }
  
  type (_, _) eff_internal_effect += Op1 : (int, bar) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op2 : (bar, foo) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op3 : (foo, int) eff_internal_effect
  
  ;;
  fun (_a : int) ->
    Call
      ( Op1,
        10,
        fun (_y : bar) ->
          Call
            ( Op2,
              _y,
              fun (_y : foo) -> Call (Op3, _y, fun (_y : int) -> Value (_a + _y))
            ) )
  ======================================================================
  codegen/test16.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect
  
  ;;
  let rec _loop _x (_x : int) = if 0 < _x then _loop (_x - 1) (_x + 1) else () in
  _loop 10 0
  ======================================================================
  codegen/test17.eff
  ----------------------------------------------------------------------
  type my_ty = Cons of my_ty
  
  ;;
  fun (Cons _argmnt : my_ty) -> Cons _argmnt
  ======================================================================
  codegen/test18.eff
  ----------------------------------------------------------------------
  type nat = Zero | Succ of nat
  
  ;;
  let rec _add _x (_x : nat) =
    match _x with Zero -> _x | Succ _n -> Succ (_add _x _n)
  in
  _add
  ======================================================================
  codegen/test19.eff
  ----------------------------------------------------------------------
  type nat = Zero | Succ of nat
  
  ;;
  fun ((_w, _k, _num) : nat * nat * int) (_x : nat * nat * int) ->
    match _x with
    | Zero, Zero, 0 -> (_w, _k, Zero, 0, 0)
    | Zero, _z, _n -> (Zero, _z, Zero, _num, _n)
    | _x, Zero, _n -> (Zero, _w, _x, 1, _n)
    | _, _, _ -> (Zero, Zero, Zero, 0, 0)
  ======================================================================
  codegen/test2.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test20.eff
  ----------------------------------------------------------------------
  let rec _even _x = _x = 0 || _odd (_x - 1)
  
  and _odd _x = if _x = 0 then false else _even (_x - 1)
  
  let even, odd = (_even, _odd)
  ======================================================================
  codegen/test21.eff
  ----------------------------------------------------------------------
  ;;
  1, true
  ======================================================================
  codegen/test3.eff
  ----------------------------------------------------------------------
  ;;
  fun (_x : float) -> _x
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
         value_clause = (fun (_id : int) -> Value _id);
         effect_clauses =
           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                (a -> (b -> _) -> _) ->
             match eff with
             | Op -> fun _n _l -> Value 2
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
  
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  
  let concat = _concat
  
  ;;
  IntNil
  ======================================================================
  codegen/two_inputs.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type int_list = Nil | Cons of (int * int_list)
  
  ;;
  let rec _op (* @ *) _x (_ys : int_list) =
    match _x with Nil -> _ys | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
  in
  let _l (_y : bool) = Cons ((if _y then 10 else 20), Nil) in
  _op (* @ *) (_l true) (_l false)
-------------------------------------------------------------------------------
