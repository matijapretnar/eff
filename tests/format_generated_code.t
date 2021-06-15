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
  codegen/capability_benchmarks.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += TripleFlip : (unit, bool) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | TripleFail : (unit, empty) eff_internal_effect
  
  type triple_int_list =
    | TripleCons of ((int * int * int) * triple_int_list)
    | TripleNil
  
  let rec _op (* @ *) _x (_ys : triple_int_list) =
    match _x with
    | TripleNil -> _ys
    | TripleCons (_x, _xs) -> TripleCons (_x, _op (* @ *) _xs _ys)
  
  let _op (* @ *) = _op (* @ *)
  
  let _testTriple (_n : int) (_s : int) =
    let rec _choice _x =
      if _x < 1 then TripleNil
      else
        let _l (_y : bool) =
          if _y then
            let rec _choice _x =
              if _x < 1 then TripleNil
              else
                let _l (_y : bool) =
                  if _y then
                    let rec _choice _x =
                      if _x < 1 then TripleNil
                      else
                        let _l (_y : bool) =
                          if _y then
                            if _x + _x + _x = _s then
                              TripleCons ((_x, _x, _x), TripleNil)
                            else TripleNil
                          else _choice (_x - 1)
                        in
                        _op (* @ *) (_l true) (_l false)
                    in
                    _choice (_x - 1)
                  else _choice (_x - 1)
                in
                _op (* @ *) (_l true) (_l false)
            in
            _choice (_x - 1)
          else _choice (_x - 1)
        in
        _op (* @ *) (_l true) (_l false)
    in
    _choice _n
  
  let testTriple = _testTriple
  
  let _handleTripleWrap ((_x, _y) : int * int) = _testTriple _x _y
  
  let handleTripleWrap = _handleTripleWrap
  
  type queen = int * int
  
  type queen_list = Nil | Cons of (queen * queen_list)
  
  type queen_list_list = QNil | QCons of (queen_list * queen_list_list)
  
  type intlist = End | Lst of (int * intlist)
  
  type option = Some of queen_list | None
  
  type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect
  
  let rec _filter _x (_x : intlist) =
    match _x with
    | End -> End
    | Lst (_x, _xs) -> if _x _x then Lst (_x, _filter _x _xs) else _filter _x _xs
  
  let filter = _filter
  
  let rec _forall _x (_x : queen_list) =
    match _x with Nil -> true | Cons (_x, _xs) -> _x _x && _forall _x _xs
  
  let forall = _forall
  
  let _no_attack ((_x, _y) : int * int) ((_x', _y') : int * int) =
    _x <> _x' && _y <> _y' && abs (_x - _x') <> abs (_y - _y')
  
  let no_attack = _no_attack
  
  let _available (_x : int) (_qs : queen_list) (_l : intlist) =
    _filter (fun (_y : int) -> _forall (_no_attack (_x, _y)) _qs) _l
  
  let available = _available
  
  let _find_solution (_n : int) =
    let rec _init _x (_acc : intlist) =
      if _x = 0 then _acc else _init (_x - 1) (Lst (_x, _acc))
    in
    let rec _place (_x, _qs) =
      if _x = _n + 1 then Some _qs
      else
        let rec _loop _x (_x : intlist) =
          match _x with
          | End -> None
          | Lst (_x, _xs) -> (
              match _x _x with None -> _loop _x _xs | Some _x -> Some _x)
        in
        _loop
          (fun (_y : int) -> _place (_x + 1, Cons ((_x, _y), _qs)))
          (_available _x _qs (_init _n End))
    in
    _place (1, Nil)
  
  let find_solution = _find_solution
  
  let _queens_all (_number_of_queens : int) = _find_solution _number_of_queens
  
  let queens_all = _queens_all
  
  type (_, _) eff_internal_effect += CountPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += CountGet : (unit, int) eff_internal_effect
  
  let rec _count _x =
    Call
      ( CountGet,
        (),
        fun (_y : int) ->
          if _y = 0 then Value _y
          else Call (CountPut, _y - 1, fun (_y : unit) -> _count ()) )
  
  let count = _count
  
  let _testCount (_m : int) =
    let rec _count _x (_s : int) = if _s = 0 then _s else _count () (_s - 1) in
    _count () _m
  
  let testCount = _testCount
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorYield : (int, unit) eff_internal_effect
  
  let _testGenerator (_n : int) =
    let rec _generateFromTo (_l, _u) (_x : int) =
      if _l > _u then _x else _generateFromTo (_l + 1, _u) (_x + _l)
    in
    _generateFromTo (1, _n) 0
  
  let testGenerator = _testGenerator
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
  codegen/interp.eff
  ----------------------------------------------------------------------
  type term =
    | Num of int
    | Add of (term * term)
    | Mul of (term * term)
    | Sub of (term * term)
    | Div of (term * term)
  
  type (_, _) eff_internal_effect += DivByZero : (unit, int) eff_internal_effect
  
  let _addCase =
    Add
      ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
        Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
  
  let addCase = _addCase
  
  let rec _createZeroCase _x =
    match _x with
    | 0 -> Sub (_addCase, _addCase)
    | _n -> Sub (_createZeroCase (_n - 1), _createZeroCase (_n - 1))
  
  let createZeroCase = _createZeroCase
  
  let rec _createCase _x =
    match _x with
    | 1 -> Div (Num 100, _createZeroCase 3)
    | _ -> Add (_addCase, _createCase (_x - 1))
  
  let createCase = _createCase
  
  let _bigTest (_num : int) =
    let rec _interp (_x, _k) =
      match _x with
      | Num _b -> _k _b
      | Add (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x + _y)))
      | Mul (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x * _y)))
      | Sub (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x - _y)))
      | Div (_l, _r) ->
          _interp
            ( _r,
              fun (_y : int) ->
                _interp
                  ( _l,
                    fun (_x : int) -> match _y with 0 -> ~-1 | _ -> _k (_x / _y)
                  ) )
    in
    _interp (_createCase _num, fun (_id : int) -> _id)
  
  let bigTest = _bigTest
  
  let _bigTestLoop (_num : int) =
    let ____finalCase = _createCase _num in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          +
          let rec _interp (_x, _k) =
            match _x with
            | Num _b -> _k _b
            | Add (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x + _y))
                  )
            | Mul (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x * _y))
                  )
            | Sub (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x - _y))
                  )
            | Div (_l, _r) ->
                _interp
                  ( _r,
                    fun (_y : int) ->
                      _interp
                        ( _l,
                          fun (_x : int) ->
                            match _y with 0 -> ~-1 | _ -> _k (_x / _y) ) )
          in
          _interp (____finalCase, fun (_id : int) -> _id))
    in
    _looper 100 0
  
  let bigTestLoop = _bigTestLoop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _testState (_n : int) =
    let rec _interp (_x, _k) =
      match _x with
      | Num _b -> fun (_ : int) -> _k _b (_b * _b)
      | Add (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x + _y)))
      | Mul (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x * _y)))
      | Sub (_l, _r) ->
          _interp
            (_l, fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x - _y)))
      | Div (_l, _r) ->
          _interp
            ( _r,
              fun (_y : int) ->
                _interp
                  ( _l,
                    fun (_x : int) ->
                      match _y with
                      | 0 -> fun (_s : int) -> _k _s _s
                      | _ -> _k (_x / _y) ) )
    in
    _interp (_createCase _n, fun (_x : int) (_ : int) -> _x) _n
  
  let testState = _testState
  
  let _testStateLoop (_n : int) =
    let _addCase =
      Add
        ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
          Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
    in
    let rec _createZeroCase _x =
      match _x with
      | 0 -> Sub (_addCase, _addCase)
      | _n -> Sub (_createZeroCase (_n - 1), _createZeroCase (_n - 1))
    in
    let rec _createCase _x =
      match _x with
      | 1 -> Div (Num 100, _createZeroCase 3)
      | _ -> Add (_addCase, _createCase (_x - 1))
    in
    let ____finalCase = _createCase _n in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          +
          let rec _interp (_x, _k) =
            match _x with
            | Num _b -> fun (_ : int) -> _k _b (_b * _b)
            | Add (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x + _y))
                  )
            | Mul (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x * _y))
                  )
            | Sub (_l, _r) ->
                _interp
                  ( _l,
                    fun (_x : int) -> _interp (_r, fun (_y : int) -> _k (_x - _y))
                  )
            | Div (_l, _r) ->
                _interp
                  ( _r,
                    fun (_y : int) ->
                      _interp
                        ( _l,
                          fun (_x : int) ->
                            match _y with
                            | 0 -> fun (_s : int) -> _k _s _s
                            | _ -> _k (_x / _y) ) )
          in
          _interp (____finalCase, fun (_x : int) (_ : int) -> _x) _n)
    in
    _looper 100 0
  
  let testStateLoop = _testStateLoop
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
  codegen/loop.eff
  ----------------------------------------------------------------------
  let rec _loop_pure _x = if _x = 0 then () else _loop_pure (_x - 1)
  
  let loop_pure = _loop_pure
  
  let _test_pure (_n : int) = _loop_pure _n
  
  let test_pure = _test_pure
  
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  
  let rec _loop_latent _x =
    if _x = 0 then Value ()
    else if _x < 0 then
      Call
        (Fail, (), fun (_y : empty) -> Value (match _y with _ -> assert false))
    else _loop_latent (_x - 1)
  
  let loop_latent = _loop_latent
  
  let _test_latent (_n : int) = _loop_latent _n
  
  let test_latent = _test_latent
  
  type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect
  
  let rec _loop_incr _x =
    if _x = 0 then Value ()
    else Call (Incr, (), fun (_y : unit) -> _loop_incr (_x - 1))
  
  let loop_incr = _loop_incr
  
  let _test_incr (_n : int) =
    let rec _loop_incr _x (_x : int) =
      if _x = 0 then _x else _loop_incr (_x - 1) (_x + 1)
    in
    _loop_incr _n 0
  
  let test_incr = _test_incr
  
  let rec _loop_incr' _x =
    if _x = 0 then Value ()
    else
      _loop_incr' (_x - 1) >>= fun _ ->
      Call (Incr, (), fun (_y : unit) -> Value _y)
  
  let loop_incr' = _loop_incr'
  
  let _test_incr' (_n : int) =
    let rec _loop_incr' (_x, _k) =
      if _x = 0 then _k ()
      else _loop_incr' (_x - 1, fun (_ : unit) (_x : int) -> _k () (_x + 1))
    and _loop_incr _x (_x : int) =
      if _x = 0 then _x else _loop_incr (_x - 1) (_x + 1)
    in
    _loop_incr' (_n, fun (_x : unit) (_x : int) -> _x) 0
  
  let test_incr' = _test_incr'
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect
  
  let rec _loop_state _x =
    if _x = 0 then Value ()
    else
      Call
        ( Get,
          (),
          fun (_y : int) ->
            Call (Put, _y + 1, fun (_y : unit) -> _loop_state (_x - 1)) )
  
  let loop_state = _loop_state
  
  let _test_state (_n : int) =
    let rec _loop_state _x (_x : int) =
      if _x = 0 then _x else _loop_state (_x - 1) (_x + 1)
    in
    _loop_state _n 0
  
  let test_state = _test_state
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
  codegen/parser.eff
  ----------------------------------------------------------------------
  Syntax error (file "codegen/parser.eff", line 25, char 11):
  parser error
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
    let _l (_y : bool) =
      if _y then IntCons (2, IntNil) else IntCons (3, IntNil)
    in
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
    if _y then
      let _l (_y : bool) =
        if _y then IntCons (10 - 0, IntNil) else IntCons (10 - 5, IntNil)
      in
      _concat (_l true) (_l false)
    else
      let _l (_y : bool) =
        if _y then IntCons (20 - 0, IntNil) else IntCons (20 - 5, IntNil)
      in
      _concat (_l true) (_l false)
  in
  _concat (_l true) (_l false)
  ======================================================================
  codegen/queens.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  
  type queen = int * int
  
  type rows = RowsEmpty | RowsCons of (int * rows)
  
  type solution = SolutionEmpty | SolutionPlace of (queen * solution)
  
  type solutions = SolutionsNil | SolutionsCons of (solution * solutions)
  
  type optional_solution = None | Some of solution
  
  type void = Void
  
  let _absurd (_void : float) = match _void with _ -> assert false
  
  let absurd = _absurd
  
  let rec _op (* @ *) _x (_ys : solutions) =
    match _x with
    | SolutionsNil -> _ys
    | SolutionsCons (_x, _xs) -> SolutionsCons (_x, _op (* @ *) _xs _ys)
  
  let _op (* @ *) = _op (* @ *)
  
  let _no_attack ((_x, _y) : int * int) ((_x', _y') : int * int) =
    _x <> _x' && _y <> _y' && abs (_x - _x') <> abs (_y - _y')
  
  let no_attack = _no_attack
  
  let rec _not_attacked _x (_qs : solution) =
    match _qs with
    | SolutionEmpty -> true
    | SolutionPlace (_x, _xs) -> _no_attack _x _x && _not_attacked _x _xs
  
  let not_attacked = _not_attacked
  
  let _available (_number_of_queens : int) (_x : int) (_qs : solution) =
    let rec _loop (_possible, _y) =
      if _y < 1 then _possible
      else if _not_attacked (_x, _y) _qs then
        _loop (RowsCons (_y, _possible), _y - 1)
      else _loop (_possible, _y - 1)
    in
    _loop (RowsEmpty, _number_of_queens)
  
  let available = _available
  
  let rec _choose _x =
    match _x with
    | RowsEmpty ->
        Call
          (Fail, (), fun (_y : empty) -> Value (match _y with _ -> assert false))
    | RowsCons (_x, _xs') ->
        Call (Decide, (), fun (_y : bool) -> if _y then Value _x else _choose _xs')
  
  let choose = _choose
  
  let _queens (_number_of_queens : int) =
    let rec _place (_x, _qs) =
      if _x > _number_of_queens then Value _qs
      else
        _choose (_available _number_of_queens _x _qs) >>= fun _y ->
        _place (_x + 1, SolutionPlace ((_x, _y), _qs))
    in
    _place (1, SolutionEmpty)
  
  let queens = _queens
  
  let _queens_one_option (_number_of_queens : int) =
    let rec _queens _number_of_queens =
      let rec _place (_x, _qs) =
        if _x > _number_of_queens then Some _qs
        else
          let rec _choose _x =
            match _x with
            | RowsEmpty -> None
            | RowsCons (_x, _xs') -> (
                let _l (_y : bool) =
                  if _y then _place (_x + 1, SolutionPlace ((_x, _x), _qs))
                  else _choose _xs'
                in
                match _l true with Some _x -> Some _x | None -> _l false)
          in
          _choose (_available _number_of_queens _x _qs)
      in
      _place (1, SolutionEmpty)
    in
    _queens _number_of_queens
  
  let queens_one_option = _queens_one_option
  
  let _queens_all (_number_of_queens : int) =
    let rec _queens _number_of_queens =
      let rec _place (_x, _qs) =
        if _x > _number_of_queens then SolutionsCons (_qs, SolutionsNil)
        else
          let rec _choose _x =
            match _x with
            | RowsEmpty -> SolutionsNil
            | RowsCons (_x, _xs') ->
                let _l (_y : bool) =
                  if _y then _place (_x + 1, SolutionPlace ((_x, _x), _qs))
                  else _choose _xs'
                in
                _op (* @ *) (_l true) (_l false)
          in
          _choose (_available _number_of_queens _x _qs)
      in
      _place (1, SolutionEmpty)
    in
    _queens _number_of_queens
  
  let queens_all = _queens_all
  
  let _queens_one_cps (_number_of_queens : int) =
    let rec _queens _number_of_queens =
      let rec _place (_x, _qs) =
        if _x > _number_of_queens then
          coer_arrow coer_refl_ty (coer_return coer_refl_ty)
            (fun (_ : unit -> solution computation) -> _qs)
        else
          let rec _choose _x (_x : unit -> solution computation) =
            match _x with
            | RowsEmpty -> _x ()
            | RowsCons (_x, _xs') ->
                let _l (_y : bool) =
                  if _y then _place (_x + 1, SolutionPlace ((_x, _x), _qs))
                  else _choose _xs'
                in
                _l true (fun (_ : unit) -> _l false _x)
          in
          _choose (_available _number_of_queens _x _qs)
      in
      _place (1, SolutionEmpty)
    in
    _queens _number_of_queens (fun (() : unit) ->
        Call
          (Fail, (), fun (_y : empty) -> Value (match _y with _ -> assert false)))
  
  let queens_one_cps = _queens_one_cps
  ======================================================================
  codegen/range.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect
  
  type int_list = Nil | Cons of (int * int_list)
  
  let _test (_n : int) =
    let rec _range (_x, _k) =
      match _x with
      | 0 -> _k Nil
      | _ -> _range (_x - 1, fun (_b : int_list) -> _k (Cons (42, _b)))
    in
    _range (_n, fun (_x : int_list) -> _x)
  
  let test = _test
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorProduce : (int, int) eff_internal_effect
  
  let _testGenerator (_m : int) =
    let rec _sum _x (_x : int) =
      if _x = 0 then _x else _sum (_x - 1) (_x + (_x mod 42))
    in
    _sum _m _m
  
  let testGenerator = _testGenerator
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
  codegen/tree.eff
  ----------------------------------------------------------------------
  type tree = Empty | Node of (tree * int * tree)
  
  type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect
  
  let _tester (_k : int) =
    let _leaf (_a : int) = Node (Empty, _a * _k, Empty) in
    let _bot (_t : tree) (_t2 : tree) =
      Node
        ( Node (Node (_t, 0, _t2), 2, _leaf 13),
          5,
          Node (_leaf 9, 7, Node (_t2, 3, Node (_leaf 3, 5, _t2))) )
    in
    _bot
      (Node (_bot (_leaf 3) (_leaf 4), 10, _bot (_leaf 1) (_leaf 3)))
      (_bot
         (Node (_bot (_leaf 3) (_leaf 4), 10, _bot (_leaf 1) (_leaf 3)))
         (_leaf 10))
  
  let tester = _tester
  
  let _max (_a : int) (_b : int) = if _a > _b then _a else _b
  
  let max = _max
  
  let _effect_max (_m : int) =
    let rec _find_max (_x, _k) =
      match _x with
      | Empty -> _k 0
      | Node (Empty, _x, Empty) -> _k _x
      | Node (_left, _x, _right) ->
          let _l (_y : bool) =
            if _y then _find_max (_left, fun (_next : int) -> _k (_x + _next))
            else _find_max (_right, fun (_next : int) -> _k (_x + _next))
          in
          _max (_l true) (_l false)
    in
    _find_max (_tester _m, fun (_x : int) -> _x)
  
  let effect_max = _effect_max
  
  let _test_max (_m : int) = _effect_max _m
  
  let test_max = _test_max
  
  let _op (_x : int) (_y : int) = _x - (3 * _y)
  
  let op = _op
  
  let _max (_a : int) (_b : int) = if _a > _b then _a else _b
  
  let max = _max
  
  type intlist = Nil | Cons of (int * intlist)
  
  let rec _op (* @ *) _x (_ys : intlist) =
    match _x with Nil -> _ys | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
  
  let _op (* @ *) = _op (* @ *)
  
  let _test_general (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    _maxl 0
      (let rec _explore (_x, _k) =
         match _x with
         | Empty -> _k 0
         | Node (_left, _x, _right) ->
             let _l (_y : bool) =
               if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
               else _explore (_right, fun (_b : int) -> _k (_op _x _b))
             in
             _op (* @ *) (_l true) (_l false)
       in
       _explore (_tester _m, fun (_x : int) -> Cons (_x, Nil)))
  
  let test_general = _test_general
  
  let _test_general_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (let rec _explore (_x, _k) =
                 match _x with
                 | Empty -> _k 0
                 | Node (_left, _x, _right) ->
                     let _l (_y : bool) =
                       if _y then
                         _explore (_left, fun (_b : int) -> _k (_op _x _b))
                       else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                     in
                     _op (* @ *) (_l true) (_l false)
               in
               _explore (____t, fun (_x : int) -> Cons (_x, Nil))))
    in
    _looper 100 0
  
  let test_general_loop = _test_general_loop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  let _absurd (_void : float) = match _void with _ -> assert false
  
  let absurd = _absurd
  
  let _test_leaf_state (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    _maxl 0
      (let rec _explore (_x, _k) =
         match _x with
         | Empty -> Call (Get, (), fun (_y : int) -> _k _y)
         | Node (_left, _x, _right) ->
             let _l (_y : bool) =
               if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
               else _explore (_right, fun (_b : int) -> _k (_op _x _b))
             in
             _l true >>= fun _b ->
             _l false >>= fun _b -> Value (_op (* @ *) _b _b)
       in
       let rec _explore (_x, _k) =
         match _x with
         | Empty -> (
             fun (_s : intlist) ->
               match _s with
               | Cons (_x, _rest) ->
                   force_unsafe
                     ((handler
                         {
                           value_clause =
                             (fun (_x : intlist) ->
                               Value (fun (_ : intlist) -> _x));
                           effect_clauses =
                             (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                  (a -> (b -> _) -> _) ->
                               match eff with
                               | Get ->
                                   fun () _l ->
                                     Value
                                       (fun (_s : intlist) ->
                                         match _s with
                                         | Cons (_x, _rest) ->
                                             coer_arrow coer_refl_ty force_unsafe
                                               _l _x _rest
                                         | Nil -> Nil)
                               | eff' -> fun arg k -> Call (eff', arg, k));
                         })
                        (_k _x))
                     _rest
               | Nil -> Nil)
         | Node (_left, _x, _right) ->
             let _l (_y : bool) =
               if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
               else _explore (_right, fun (_b : int) -> _k (_op _x _b))
             in
             force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_b : intlist) ->
                         Value
                           (force_unsafe
                              ((handler
                                  {
                                    value_clause =
                                      (fun (_b : intlist) ->
                                        Value
                                          (fun (_ : intlist) -> _op (* @ *) _b _b));
                                    effect_clauses =
                                      (fun (type a b)
                                           (eff : (a, b) eff_internal_effect) :
                                           (a -> (b -> _) -> _) ->
                                        match eff with
                                        | Get ->
                                            fun () _l ->
                                              Value
                                                (fun (_s : intlist) ->
                                                  match _s with
                                                  | Cons (_x, _rest) ->
                                                      coer_arrow coer_refl_ty
                                                        force_unsafe _l _x _rest
                                                  | Nil -> Nil)
                                        | eff' -> fun arg k -> Call (eff', arg, k));
                                  })
                                 (_l false))));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l ->
                               Value
                                 (fun (_s : intlist) ->
                                   match _s with
                                   | Cons (_x, _rest) ->
                                       coer_arrow coer_refl_ty force_unsafe _l _x
                                         _rest
                                   | Nil -> Nil)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_l true))
       in
       _explore
         (_tester _m, fun (_x : int) -> Value (Cons (_x, Nil)))
         (_populate_leafs 0 154))
  
  let test_leaf_state = _test_leaf_state
  
  let _test_leaf_state_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    let ____leafs = _populate_leafs 0 154 in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (let rec _explore (_x, _k) =
                 match _x with
                 | Empty -> Call (Get, (), fun (_y : int) -> _k _y)
                 | Node (_left, _x, _right) ->
                     let _l (_y : bool) =
                       if _y then
                         _explore (_left, fun (_b : int) -> _k (_op _x _b))
                       else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                     in
                     _l true >>= fun _b ->
                     _l false >>= fun _b -> Value (_op (* @ *) _b _b)
               in
               let rec _explore (_x, _k) =
                 match _x with
                 | Empty -> (
                     fun (_s : intlist) ->
                       match _s with
                       | Cons (_x, _rest) ->
                           force_unsafe
                             ((handler
                                 {
                                   value_clause =
                                     (fun (_x : intlist) ->
                                       Value (fun (_ : intlist) -> _x));
                                   effect_clauses =
                                     (fun (type a b)
                                          (eff : (a, b) eff_internal_effect) :
                                          (a -> (b -> _) -> _) ->
                                       match eff with
                                       | Get ->
                                           fun () _l ->
                                             Value
                                               (fun (_s : intlist) ->
                                                 match _s with
                                                 | Cons (_x, _rest) ->
                                                     coer_arrow coer_refl_ty
                                                       force_unsafe _l _x _rest
                                                 | Nil -> Nil)
                                       | eff' -> fun arg k -> Call (eff', arg, k));
                                 })
                                (_k _x))
                             _rest
                       | Nil -> Nil)
                 | Node (_left, _x, _right) ->
                     let _l (_y : bool) =
                       if _y then
                         _explore (_left, fun (_b : int) -> _k (_op _x _b))
                       else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                     in
                     force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_b : intlist) ->
                                 Value
                                   (force_unsafe
                                      ((handler
                                          {
                                            value_clause =
                                              (fun (_b : intlist) ->
                                                Value
                                                  (fun (_ : intlist) ->
                                                    _op (* @ *) _b _b));
                                            effect_clauses =
                                              (fun (type a b)
                                                   (eff :
                                                     (a, b) eff_internal_effect) :
                                                   (a -> (b -> _) -> _) ->
                                                match eff with
                                                | Get ->
                                                    fun () _l ->
                                                      Value
                                                        (fun (_s : intlist) ->
                                                          match _s with
                                                          | Cons (_x, _rest) ->
                                                              coer_arrow
                                                                coer_refl_ty
                                                                force_unsafe _l _x
                                                                _rest
                                                          | Nil -> Nil)
                                                | eff' ->
                                                    fun arg k ->
                                                      Call (eff', arg, k));
                                          })
                                         (_l false))));
                             effect_clauses =
                               (fun (type a b) (eff : (a, b) eff_internal_effect)
                                    : (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun () _l ->
                                       Value
                                         (fun (_s : intlist) ->
                                           match _s with
                                           | Cons (_x, _rest) ->
                                               coer_arrow coer_refl_ty
                                                 force_unsafe _l _x _rest
                                           | Nil -> Nil)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_l true))
               in
               _explore
                 (____t, fun (_x : int) -> Value (Cons (_x, Nil)))
                 ____leafs))
    in
    _looper 100 0
  
  let test_leaf_state_loop = _test_leaf_state_loop
  
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _test_leaf_state_update (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    _maxl 0
      (let rec _explore (_x, _k) =
         match _x with
         | Empty -> Call (Get, (), fun (_y : int) -> _k _y)
         | Node (_left, _x, _right) ->
             Call
               ( Set,
                 _x * _x,
                 fun (_y : unit) ->
                   let _l (_y : bool) =
                     if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
                     else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                   in
                   _l true >>= fun _b ->
                   _l false >>= fun _b -> Value (_op (* @ *) _b _b) )
       in
       let rec _explore (_x, _k) (_x : int) =
         match _x with
         | Empty ->
             force_unsafe
               ((handler
                   {
                     value_clause =
                       (fun (_x : intlist) -> Value (fun (_ : int) -> _x));
                     effect_clauses =
                       (fun (type a b) (eff : (a, b) eff_internal_effect) :
                            (a -> (b -> _) -> _) ->
                         match eff with
                         | Get ->
                             fun () _l ->
                               Value
                                 (fun (_s : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l _s _s)
                         | Set ->
                             fun _s _l ->
                               Value
                                 (fun (_ : int) ->
                                   coer_arrow coer_refl_ty force_unsafe _l () _s)
                         | eff' -> fun arg k -> Call (eff', arg, k));
                   })
                  (_k _x))
               _x
         | Node (_left, _x, _right) ->
             (let _l (_y : bool) =
                if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
                else _explore (_right, fun (_b : int) -> _k (_op _x _b))
              in
              force_unsafe
                ((handler
                    {
                      value_clause =
                        (fun (_b : intlist) ->
                          Value
                            (force_unsafe
                               ((handler
                                   {
                                     value_clause =
                                       (fun (_b : intlist) ->
                                         Value
                                           (fun (_ : int) -> _op (* @ *) _b _b));
                                     effect_clauses =
                                       (fun (type a b)
                                            (eff : (a, b) eff_internal_effect) :
                                            (a -> (b -> _) -> _) ->
                                         match eff with
                                         | Get ->
                                             fun () _l ->
                                               Value
                                                 (fun (_s : int) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l _s _s)
                                         | Set ->
                                             fun _s _l ->
                                               Value
                                                 (fun (_ : int) ->
                                                   coer_arrow coer_refl_ty
                                                     force_unsafe _l () _s)
                                         | eff' -> fun arg k -> Call (eff', arg, k));
                                   })
                                  (_l false))));
                      effect_clauses =
                        (fun (type a b) (eff : (a, b) eff_internal_effect) :
                             (a -> (b -> _) -> _) ->
                          match eff with
                          | Get ->
                              fun () _l ->
                                Value
                                  (fun (_s : int) ->
                                    coer_arrow coer_refl_ty force_unsafe _l _s _s)
                          | Set ->
                              fun _s _l ->
                                Value
                                  (fun (_ : int) ->
                                    coer_arrow coer_refl_ty force_unsafe _l () _s)
                          | eff' -> fun arg k -> Call (eff', arg, k));
                    })
                   (_l true)))
               (_x * _x)
       in
       _explore (_tester _m, fun (_x : int) -> Value (Cons (_x, Nil))) ~-1)
  
  let test_leaf_state_update = _test_leaf_state_update
  
  let _test_leaf_state_update_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (let rec _explore (_x, _k) =
                 match _x with
                 | Empty -> Call (Get, (), fun (_y : int) -> _k _y)
                 | Node (_left, _x, _right) ->
                     Call
                       ( Set,
                         _x * _x,
                         fun (_y : unit) ->
                           let _l (_y : bool) =
                             if _y then
                               _explore (_left, fun (_b : int) -> _k (_op _x _b))
                             else
                               _explore (_right, fun (_b : int) -> _k (_op _x _b))
                           in
                           _l true >>= fun _b ->
                           _l false >>= fun _b -> Value (_op (* @ *) _b _b) )
               in
               let rec _explore (_x, _k) (_x : int) =
                 match _x with
                 | Empty ->
                     force_unsafe
                       ((handler
                           {
                             value_clause =
                               (fun (_x : intlist) -> Value (fun (_ : int) -> _x));
                             effect_clauses =
                               (fun (type a b) (eff : (a, b) eff_internal_effect)
                                    : (a -> (b -> _) -> _) ->
                                 match eff with
                                 | Get ->
                                     fun () _l ->
                                       Value
                                         (fun (_s : int) ->
                                           coer_arrow coer_refl_ty force_unsafe _l
                                             _s _s)
                                 | Set ->
                                     fun _s _l ->
                                       Value
                                         (fun (_ : int) ->
                                           coer_arrow coer_refl_ty force_unsafe _l
                                             () _s)
                                 | eff' -> fun arg k -> Call (eff', arg, k));
                           })
                          (_k _x))
                       _x
                 | Node (_left, _x, _right) ->
                     (let _l (_y : bool) =
                        if _y then
                          _explore (_left, fun (_b : int) -> _k (_op _x _b))
                        else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                      in
                      force_unsafe
                        ((handler
                            {
                              value_clause =
                                (fun (_b : intlist) ->
                                  Value
                                    (force_unsafe
                                       ((handler
                                           {
                                             value_clause =
                                               (fun (_b : intlist) ->
                                                 Value
                                                   (fun (_ : int) ->
                                                     _op (* @ *) _b _b));
                                             effect_clauses =
                                               (fun (type a b)
                                                    (eff :
                                                      (a, b) eff_internal_effect)
                                                    : (a -> (b -> _) -> _) ->
                                                 match eff with
                                                 | Get ->
                                                     fun () _l ->
                                                       Value
                                                         (fun (_s : int) ->
                                                           coer_arrow coer_refl_ty
                                                             force_unsafe _l _s _s)
                                                 | Set ->
                                                     fun _s _l ->
                                                       Value
                                                         (fun (_ : int) ->
                                                           coer_arrow coer_refl_ty
                                                             force_unsafe _l () _s)
                                                 | eff' ->
                                                     fun arg k ->
                                                       Call (eff', arg, k));
                                           })
                                          (_l false))));
                              effect_clauses =
                                (fun (type a b) (eff : (a, b) eff_internal_effect)
                                     : (a -> (b -> _) -> _) ->
                                  match eff with
                                  | Get ->
                                      fun () _l ->
                                        Value
                                          (fun (_s : int) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l _s _s)
                                  | Set ->
                                      fun _s _l ->
                                        Value
                                          (fun (_ : int) ->
                                            coer_arrow coer_refl_ty force_unsafe
                                              _l () _s)
                                  | eff' -> fun arg k -> Call (eff', arg, k));
                            })
                           (_l true)))
                       (_x * _x)
               in
               _explore (____t, fun (_x : int) -> Value (Cons (_x, Nil))) ~-1))
    in
    _looper 100 0
  
  let test_leaf_state_update_loop = _test_leaf_state_update_loop
  
  let _test_leaf_state_update_merged_handler (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    _maxl 0
      (let rec _explore (_x, _k) (_x : int) =
         match _x with
         | Empty -> _k _x _x
         | Node (_left, _x, _right) ->
             (let _l (_y : bool) =
                if _y then _explore (_left, fun (_b : int) -> _k (_op _x _b))
                else _explore (_right, fun (_b : int) -> _k (_op _x _b))
              in
              fun (_s : int) -> _op (* @ *) (_l true _s) (_l false _s))
               (_x * _x)
       in
       _explore (_tester _m, fun (_x : int) (_ : int) -> Cons (_x, Nil)) ~-1)
  
  let test_leaf_state_update_merged_handler =
    _test_leaf_state_update_merged_handler
  
  let _test_leaf_state_update_merged_handler_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (let rec _explore (_x, _k) (_x : int) =
                 match _x with
                 | Empty -> _k _x _x
                 | Node (_left, _x, _right) ->
                     (let _l (_y : bool) =
                        if _y then
                          _explore (_left, fun (_b : int) -> _k (_op _x _b))
                        else _explore (_right, fun (_b : int) -> _k (_op _x _b))
                      in
                      fun (_s : int) -> _op (* @ *) (_l true _s) (_l false _s))
                       (_x * _x)
               in
               _explore (____t, fun (_x : int) (_ : int) -> Cons (_x, Nil)) ~-1))
    in
    _looper 100 0
  
  let test_leaf_state_update_merged_handler_loop =
    _test_leaf_state_update_merged_handler_loop
  ======================================================================
  codegen/two_inputs.eff
  ----------------------------------------------------------------------
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  type int_list = Nil | Cons of (int * int_list)
  
  ;;
  let rec _op (* @ *) _x (_ys : int_list) =
    match _x with Nil -> _ys | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
  in
  let _l (_y : bool) = if _y then Cons (10, Nil) else Cons (20, Nil) in
  _op (* @ *) (_l true) (_l false)
-------------------------------------------------------------------------------
