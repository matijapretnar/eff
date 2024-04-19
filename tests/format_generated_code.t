  $ for f in codegen/*.eff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "----------------------------------------------------------------------"
  >   ../eff.exe --no-stdlib --compile-plain-ocaml --no-header $f | sed -E 's/_[0-9]+//g' | sed -E "s/'ty[0-9]+/'ty/g" > $f.ml
  >   ocamlformat --enable-outside-detected-project $f.ml
  > done
  ======================================================================
  codegen/application_red.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  3 * 2
  ======================================================================
  codegen/break-split.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two = 2
  let two = _two
  let _three = 3
  let three = _three;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun (() : unit) _k ->
                    Value
                      (coer_arrow coer_refl_ty force_unsafe _k true
                      + coer_arrow coer_refl_ty force_unsafe _k false)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (let rec _f _x =
          Call (Decide, (), fun (_y : bool) -> Value (if _y then 2 else 3))
        in
        _f ()))
  ======================================================================
  codegen/capability_benchmarks.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
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
      if _x < 1 then
        Call
          ( TripleFail,
            (),
            fun (_y : empty) -> Value (match _y with _ -> assert false) )
      else
        Call
          ( TripleFlip,
            (),
            fun (_y : bool) -> if _y then Value _x else _choice (_x - 1) )
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : triple_int_list) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | TripleFail -> fun (_ : unit) _k -> Value TripleNil
                | TripleFlip ->
                    fun (() : unit) _k ->
                      Value
                        (_op (* @ *)
                           (coer_arrow coer_refl_ty force_unsafe _k true)
                           (coer_arrow coer_refl_ty force_unsafe _k false))
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : triple_int_list) -> Value _x))
         ( _choice _n >>= fun _i ->
           _choice (_i - 1) >>= fun _j ->
           _choice (_j - 1) >>= fun _k ->
           (if _i + _j + _k = _s then Value (_i, _j, _k)
            else
              Call
                ( TripleFail,
                  (),
                  fun (_y : empty) -> Value (match _y with _ -> assert false) ))
           >>= fun _r -> Value (TripleCons (_r, TripleNil)) ))
  
  let testTriple = _testTriple
  let _handleTripleWrap ((_x, _y) : int * int) = _testTriple _x _y
  let handleTripleWrap = _handleTripleWrap
  
  type queen = int * int
  type queen_list = Nil | Cons of ((int * int) * queen_list)
  type queen_list_list = QNil | QCons of (queen_list * queen_list_list)
  type intlist = End | Lst of (int * intlist)
  type option = Some of queen_list | None
  type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect
  
  let rec _filter _x (_x : intlist) =
    match _x with
    | End -> Value End
    | Lst (_x, _xs) ->
        _x _x >>= fun _b ->
        if _b then _filter _x _xs >>= fun _b -> Value (Lst (_x, _b))
        else _filter _x _xs
  
  let filter = _filter
  
  let rec _forall _x (_x : queen_list) =
    match _x with
    | Nil -> Value true
    | Cons (_x, _xs) ->
        _x _x >>= fun _b -> if _b then _forall _x _xs else Value false
  
  let forall = _forall
  
  let _no_attack ((_x, _y) : int * int) ((_x', _y') : int * int) =
    _x <> _x' && _y <> _y' && abs (_x - _x') <> abs (_y - _y')
  
  let no_attack = _no_attack
  
  let _available (_x : int) (_qs : queen_list) (_l : intlist) =
    coer_arrow
      (coer_arrow coer_refl_ty (coer_return coer_refl_ty))
      (coer_arrow coer_refl_ty force_unsafe)
      _filter
      (fun (_y : int) ->
        coer_arrow
          (coer_arrow coer_refl_ty (coer_return coer_refl_ty))
          (coer_arrow coer_refl_ty force_unsafe)
          _forall
          (_no_attack (_x, _y))
          _qs)
      _l
  
  let available = _available
  
  let _find_solution (_n : int) =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : option) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Select ->
                    fun (_lst : intlist) _k ->
                      Value
                        (let rec _loop _x (_x : intlist) =
                           match _x with
                           | End -> None
                           | Lst (_x, _xs) -> (
                               match _x _x with
                               | None -> _loop _x _xs
                               | Some _x -> Some _x)
                         in
                         _loop (coer_arrow coer_refl_ty force_unsafe _k) _lst)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : option) -> Value _x))
         (let rec _init _x (_acc : intlist) =
            if _x = 0 then _acc else _init (_x - 1) (Lst (_x, _acc))
          in
          let ____l = _init _n End in
          let rec _place (_x, _qs) =
            if _x = _n + 1 then Value (Some _qs)
            else
              Call
                ( Select,
                  _available _x _qs ____l,
                  fun (_y : int) -> _place (_x + 1, Cons ((_x, _y), _qs)) )
          in
          _place (1, Nil)))
  
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
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : int) -> Value (fun (_x : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | CountGet ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k _s _s)
                | CountPut ->
                    fun (_s : int) _k ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () _s)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         (_count ()))
      _m
  
  let testCount = _testCount
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorYield : (int, unit) eff_internal_effect
  
  let _testGenerator (_n : int) =
    let rec _generateFromTo (_l, _u) =
      if _l > _u then Value ()
      else
        Call (GeneratorYield, _l, fun (_y : unit) -> _generateFromTo (_l + 1, _u))
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : unit) -> Value (fun (_s : int) -> _s));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | GeneratorPut ->
                    fun (_s' : int) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () _s')
                | GeneratorGet ->
                    fun (_ : unit) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k _s _s)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         ((handler
             {
               value_clause = (fun (_id : unit) -> Value _id);
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | GeneratorYield ->
                       fun (_e : int) _k ->
                         Call
                           ( GeneratorGet,
                             (),
                             fun (_y : int) ->
                               Call
                                 (GeneratorPut, _y + _e, fun (_y : unit) -> _k ())
                           )
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : unit) -> Value _x))
            (_generateFromTo (1, _n))))
      0
  
  let testGenerator = _testGenerator
  ======================================================================
  codegen/compose.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _compose _tycoer _tycoer _tycoer _tycoer _tycoer
      (_f : 'ty -> 'ty computation) (_g : 'ty -> 'ty computation) (_x : 'ty) =
    coer_computation _tycoer (coer_computation _tycoer (_g (_tycoer _x)))
    >>= fun _b -> coer_computation _tycoer (_f (_tycoer _b))
  
  let compose = _compose
  ======================================================================
  codegen/constant_folding_match.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
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
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type int_list = Nil | Cons of (int * int_list)
  
  let _f (_y : int_list) =
    (match _y with
    | Nil -> 1
    | Cons (_x, Nil) -> _x
    | Cons (_, Cons (_y, Nil)) -> _y
    | Cons (_x, _) -> _x)
    + 10
  
  let f = _f;;
  
  4 + 10
  ======================================================================
  codegen/handle_rec.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Eff : (unit, unit) eff_internal_effect;;
  
  let rec _f _x =
    if _x = 0 then Value 1 else Call (Eff, (), fun (_y : unit) -> _f (_x - 1))
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id : int) -> Value _id);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Eff ->
                  fun (() : unit) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k () * 2)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (_f 5))
  ;;
  
  let rec _g _x = if _x = 0 then 1 else _g (_x - 1) in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_id : int) -> Value _id);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Eff ->
                  fun (() : unit) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k () * 2)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Value (_g 5)))
  ======================================================================
  codegen/handler_beta_reduction.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Eff : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value (_x + 4));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Eff ->
                  fun (_x : int) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k (_x + 2))
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Eff, 1 + 3, fun (_y : int) -> Value _y)))
  ======================================================================
  codegen/ifthenelse.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  ()
  ======================================================================
  codegen/interp.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
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
    let rec _interp _x =
      match _x with
      | Num _b -> Value _b
      | Add (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x + _y)
      | Mul (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x * _y)
      | Sub (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x - _y)
      | Div (_l, _r) -> (
          _interp _r >>= fun _y ->
          _interp _l >>= fun _x ->
          match _y with
          | 0 -> Call (DivByZero, (), fun (_y : int) -> Value _y)
          | _ -> Value (_x / _y))
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : int) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | DivByZero -> fun (() : unit) _k -> Value (( ~- ) 1)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int) -> Value _x))
         (_interp (_createCase _num)))
  
  let bigTest = _bigTest
  
  let _bigTestLoop (_num : int) =
    let rec _interp _x =
      match _x with
      | Num _b -> Value _b
      | Add (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x + _y)
      | Mul (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x * _y)
      | Sub (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x - _y)
      | Div (_l, _r) -> (
          _interp _r >>= fun _y ->
          _interp _l >>= fun _x ->
          match _y with
          | 0 -> Call (DivByZero, (), fun (_y : int) -> Value _y)
          | _ -> Value (_x / _y))
    in
    let ____finalCase = _createCase _num in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + force_unsafe
              ((handler
                  {
                    value_clause = (fun (_id : int) -> Value _id);
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | DivByZero -> fun (() : unit) _k -> Value (( ~- ) 1)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  }
                  (fun (_x : int) -> Value _x))
                 (_interp ____finalCase)))
    in
    _looper 100 0
  
  let bigTestLoop = _bigTestLoop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _testState (_n : int) =
    let rec _interp _x =
      match _x with
      | Num _b -> Call (Set, _b * _b, fun (_y : unit) -> Value _b)
      | Add (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x + _y)
      | Mul (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x * _y)
      | Sub (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x - _y)
      | Div (_l, _r) -> (
          _interp _r >>= fun _y ->
          _interp _l >>= fun _x ->
          match _y with
          | 0 -> Call (Get, (), fun (_y : int) -> Value _y)
          | _ -> Value (_x / _y))
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : int) -> Value (fun (_ : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k _s _s)
                | Set ->
                    fun (_s : int) _k ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () _s)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         (_interp (_createCase _n)))
      _n
  
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
    let rec _interp _x =
      match _x with
      | Num _b -> Call (Set, _b * _b, fun (_y : unit) -> Value _b)
      | Add (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x + _y)
      | Mul (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x * _y)
      | Sub (_l, _r) ->
          _interp _l >>= fun _x ->
          _interp _r >>= fun _y -> Value (_x - _y)
      | Div (_l, _r) -> (
          _interp _r >>= fun _y ->
          _interp _l >>= fun _x ->
          match _y with
          | 0 -> Call (Get, (), fun (_y : int) -> Value _y)
          | _ -> Value (_x / _y))
    in
    let ____finalCase = _createCase _n in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + force_unsafe
              ((handler
                  {
                    value_clause = (fun (_x : int) -> Value (fun (_ : int) -> _x));
                    effect_clauses =
                      (fun (type a b) (eff : (a, b) eff_internal_effect) :
                           (a -> (b -> _) -> _) ->
                        match eff with
                        | Get ->
                            fun (() : unit) _k ->
                              Value
                                (fun (_s : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _k _s _s)
                        | Set ->
                            fun (_s : int) _k ->
                              Value
                                (fun (_ : int) ->
                                  coer_arrow coer_refl_ty force_unsafe _k () _s)
                        | eff' -> fun arg k -> Call (eff', arg, k));
                  }
                  (fun (_x : int -> int) -> Value _x))
                 (_interp ____finalCase))
              _n)
    in
    _looper 100 0
  
  let testStateLoop = _testStateLoop
  ======================================================================
  codegen/is_relatively_pure.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op1 : (int, unit) eff_internal_effect
  type (_, _) eff_internal_effect += Op2 : (int, unit) eff_internal_effect;;
  
  (handler
     {
       value_clause = (fun (_x : unit) -> Value _x);
       effect_clauses =
         (fun (type a b) (eff : (a, b) eff_internal_effect) : (a -> (b -> _) -> _) ->
           match eff with
           | Op2 -> fun (_n : int) _k -> _k ()
           | eff' -> fun arg k -> Call (eff', arg, k));
     }
     (fun (_x : unit) -> Value _x))
    (Call (Op1, 1, fun (_y : unit) -> Value _y))
  ======================================================================
  codegen/let_list_to_bind.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  2 + 1
  ======================================================================
  codegen/loop.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
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
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : unit) -> Value (fun (_x : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Incr ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_x : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () (_x + 1))
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         (_loop_incr _n))
      0
  
  let test_incr = _test_incr
  
  let rec _loop_incr' _x =
    if _x = 0 then Value ()
    else
      _loop_incr' (_x - 1) >>= fun _ ->
      Call (Incr, (), fun (_y : unit) -> Value _y)
  
  let loop_incr' = _loop_incr'
  
  let _test_incr' (_n : int) =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : unit) -> Value (fun (_x : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Incr ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_x : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () (_x + 1))
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         (_loop_incr' _n))
      0
  
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
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : unit) -> Value (fun (_x : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k _s _s)
                | Put ->
                    fun (_s' : int) _k ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () _s')
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         (_loop_state _n))
      0
  
  let test_state = _test_state
  ======================================================================
  codegen/map.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let rec _map _tycoer _tycoer _tycoer _tycoer _tycoer _x (_x : 'ty list) =
    match _x with
    | [] -> coer_return (coer_list _tycoer) []
    | _x :: _xs ->
        coer_computation _tycoer (coer_computation _tycoer (_x (_tycoer _x)))
        >>= fun _b ->
        _map _tycoer _tycoer _tycoer _tycoer _tycoer _x _xs >>= fun _b ->
        Value
          ((fun (x, xs) -> x :: xs) (coer_tuple (_tycoer, coer_refl_ty) (_b, _b)))
  
  let map = _map
  ======================================================================
  codegen/match_red.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  1
  ======================================================================
  codegen/nested_handlers.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  type (_, _) eff_internal_effect += Fail : (unit, unit) eff_internal_effect
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _test_nested (_m : int) =
    let rec _simple _x = Call (Get, (), fun (_y : int) -> Value _y) in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : int) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Get ->
                    fun (() : unit) _k ->
                      Value (coer_arrow coer_refl_ty force_unsafe _k _m)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int) -> Value _x))
         ((handler
             {
               value_clause = (fun (_x : int) -> Value _x);
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : int) -> Value _x))
            (_simple ())))
  
  let test_nested = _test_nested
  
  let _test_nested (_m : int) =
    let rec _go _x =
      if _x = 0 then Call (Fail, (), fun (_y : unit) -> Value _y)
      else
        Call
          ( Decide,
            (),
            fun (_y : bool) -> if _y then _go (_x - 1) else _go (_x - 2) )
    in
    (handler
       {
         value_clause = (fun (_id : unit) -> Value _id);
         effect_clauses =
           (fun (type a b) (eff : (a, b) eff_internal_effect) :
                (a -> (b -> _) -> _) ->
             match eff with
             | Decide ->
                 fun (() : unit) _k ->
                   (handler
                      {
                        value_clause = (fun (_id : unit) -> Value _id);
                        effect_clauses =
                          (fun (type a b) (eff : (a, b) eff_internal_effect) :
                               (a -> (b -> _) -> _) ->
                            match eff with
                            | Fail -> fun (() : unit) __k -> _k false
                            | eff' -> fun arg k -> Call (eff', arg, k));
                      }
                      (fun (_x : unit) -> Value _x))
                     (_k true)
             | eff' -> fun arg k -> Call (eff', arg, k));
       }
       (fun (_x : unit) -> Value _x))
      (_go _m)
  
  let test_nested = _test_nested
  ======================================================================
  codegen/norec.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _f (_x : 'ty) = ()
  let f = _f
  ======================================================================
  codegen/not-found.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op1 ->
                  fun (_x : int) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k 11)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Op1, 5, fun (_y : int) -> Value _y)))
  ======================================================================
  codegen/one_input.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun (() : unit) _k ->
                    Value
                      (coer_arrow coer_refl_ty force_unsafe _k true
                      + coer_arrow coer_refl_ty force_unsafe _k false)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Decide, (), fun (_y : bool) -> Value (if _y then 10 else 20))))
  ======================================================================
  codegen/optimize_pattern_match.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _k (_b : int) =
    let rec _a (_x, _y) (_z : int) = _x + _y + _z + _b in
    _a
  
  let k = _k
  ======================================================================
  codegen/optimize_short_circuit.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _a (_b : bool) (_c : bool) = _b && _c
  let a = _a
  ======================================================================
  codegen/original.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  let rec _loop _x = if _x = 0 then 0 else _loop (_x - 1) in
  _loop 10
  ======================================================================
  codegen/other-effect.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += WriteInt : (int, unit) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : unit) -> Value 0);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | WriteInt ->
                  fun (_n : int) _k ->
                    Value (_n + coer_arrow coer_refl_ty force_unsafe _k ())
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (let rec _f _x =
          Call
            ( WriteInt,
              _x,
              fun (_y : unit) -> if _x = 0 then Value () else _f (_x - 1) )
        in
        _f 10))
  ======================================================================
  codegen/parser.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _absurd _tycoer (_void : 'ty) = match _tycoer _void with _ -> assert false
  let absurd = _absurd
  
  let rec _op (* @ *) _tycoer _tycoer _x (_ys : 'ty list) =
    match _x with
    | [] -> coer_list _tycoer _ys
    | _x :: _xs ->
        (fun (x, xs) -> x :: xs)
          (coer_tuple (_tycoer, coer_refl_ty)
             (_x, _op (* @ *) _tycoer _tycoer _xs _ys))
  
  let _op (* @ *) = _op (* @ *)
  
  type (_, _) eff_internal_effect += Symbol : (string, string) eff_internal_effect
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _fail (() : unit) =
    Call (Fail, (), fun (_y : empty) -> Value (match _y with _ -> assert false))
  
  let fail = _fail
  
  let _parse _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer
      _tycoer _tycoer _tycoer _tycoer _cmd =
    handler
      {
        value_clause =
          (fun (_x : 'ty) ->
            coer_return
              (coer_arrow coer_refl_ty (coer_computation _tycoer))
              (coer_arrow coer_refl_ty (coer_computation _tycoer)
                 (fun (_s : string list) ->
                   match _s with
                   | [] -> coer_return _tycoer (_tycoer _x)
                   | _ ->
                       coer_computation _tycoer
                         (coer_computation _tycoer (_fail ())))));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Symbol ->
                fun (_c : string) _k ->
                  Value
                    (fun (_s : string list) ->
                      match _s with
                      | [] ->
                          coer_computation _tycoer
                            (coer_computation _tycoer (_fail ()))
                      | _x :: _xs ->
                          if _c = _x then _k _x >>= fun _b -> _b _xs
                          else
                            coer_computation _tycoer
                              (coer_computation _tycoer (_fail ())))
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : string list -> 'ty computation) ->
        coer_return
          (coer_arrow coer_refl_ty (coer_computation _tycoer))
          (coer_arrow coer_refl_ty (coer_computation _tycoer) _x))
      _cmd
  
  let parse = _parse
  
  let _allsols _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer
      _cmd =
    handler
      {
        value_clause =
          (fun (_x : 'ty) ->
            coer_return (coer_list _tycoer)
              (coer_list _tycoer
                 ((fun (x, xs) -> x :: xs)
                    (coer_tuple (_tycoer, coer_list _tycoer) (_tycoer _x, [])))));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Decide ->
                fun (_ : unit) _k ->
                  _k true >>= fun _b ->
                  _k false >>= fun _b ->
                  Value (_op (* @ *) coer_refl_ty coer_refl_ty _b _b)
            | Fail -> fun (_ : unit) _ -> coer_return (coer_list _tycoer) []
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty list) ->
        coer_return (coer_list _tycoer) (coer_list _tycoer _x))
      _cmd
  
  let allsols = _allsols
  
  let _backtrack _tycoer _tycoer _tycoer _cmd =
    handler
      {
        value_clause = (fun (_id : 'ty) -> coer_return _tycoer _id);
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with
            | Decide ->
                fun (_ : unit) _k ->
                  (handler
                     {
                       value_clause = (fun (_id : 'ty) -> Value _id);
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Fail -> fun (_ : unit) _ -> _k false
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : 'ty) -> Value _x))
                    (_k true)
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty) -> coer_return _tycoer (_tycoer _x))
      _cmd
  
  let backtrack = _backtrack
  let _createNumber ((_prev, _num) : int * int) = (_prev * 10) + _num
  let createNumber = _createNumber
  
  let rec _parseNum (_l, _v) =
    match _l with
    | [] -> Value _v
    | _x :: _xs -> (
        match _x with
        | "0" -> _parseNum (_xs, _createNumber (_v, 0))
        | "1" -> _parseNum (_xs, _createNumber (_v, 1))
        | "2" -> _parseNum (_xs, _createNumber (_v, 2))
        | "3" -> _parseNum (_xs, _createNumber (_v, 3))
        | "4" -> _parseNum (_xs, _createNumber (_v, 4))
        | "5" -> _parseNum (_xs, _createNumber (_v, 5))
        | "6" -> _parseNum (_xs, _createNumber (_v, 6))
        | "7" -> _parseNum (_xs, _createNumber (_v, 7))
        | "8" -> _parseNum (_xs, _createNumber (_v, 8))
        | "9" -> _parseNum (_xs, _createNumber (_v, 9))
        | _ -> _fail ())
  
  let parseNum = _parseNum
  let rec _toNum _x = _parseNum (_x, 0)
  let toNum = _toNum
  
  let _digit (() : unit) =
    let rec _checkNums _x =
      match _x with
      | [] -> _fail ()
      | _x :: _xs ->
          Call
            ( Decide,
              (),
              fun (_y : bool) ->
                if _y then Call (Symbol, _x, fun (_y : string) -> Value _y)
                else _checkNums _xs )
    in
    _checkNums [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ]
  
  let digit = _digit
  
  let rec _many _tycoer _tycoer _tycoer _tycoer _tycoer _x =
    Call
      ( Decide,
        (),
        fun (_y : bool) ->
          coer_computation (coer_list _tycoer)
            (if _y then
               coer_computation (coer_list _tycoer)
                 (coer_computation (coer_list _tycoer)
                    (coer_computation (coer_list _tycoer) (_x ())))
             else coer_return (coer_list _tycoer) []) )
  
  let many = _many
  
  let rec _many1 _x =
    _digit () >>= fun _x ->
    _many coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty _many1
    >>= fun _xs -> Value (_op (* @ *) coer_refl_ty coer_refl_ty (_x :: []) _xs)
  
  let many1 = _many1
  
  let rec _expr _x =
    let rec _term _x =
      let rec _factor _x =
        Call
          ( Decide,
            (),
            fun (_y : bool) ->
              if _y then _many1 () >>= fun _i -> _toNum _i
              else
                Call
                  ( Symbol,
                    "(",
                    fun (_y : string) ->
                      _expr () >>= fun _j ->
                      Call (Symbol, ")", fun (_y : string) -> Value _j) ) )
      in
      Call
        ( Decide,
          (),
          fun (_y : bool) ->
            if _y then
              _factor () >>= fun _i ->
              Call
                ( Symbol,
                  "*",
                  fun (_y : string) -> _term () >>= fun _j -> Value (_i * _j) )
            else _factor () )
    in
    Call
      ( Decide,
        (),
        fun (_y : bool) ->
          if _y then
            _term () >>= fun _i ->
            Call
              ( Symbol,
                "+",
                fun (_y : string) -> _expr () >>= fun _j -> Value (_i + _j) )
          else _term () )
  
  let expr = _expr
  
  let _parseTest (() : unit) =
    force_unsafe
      (_allsols coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
         coer_refl_ty coer_refl_ty coer_refl_ty
         ( _parse coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
             coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
             coer_refl_ty coer_refl_ty (_expr ())
         >>= fun _b -> _b [ "4"; "3"; "*"; "("; "3"; "+"; "3"; ")" ] ))
  
  let parseTest = _parseTest
  let _x = _parseTest ()
  let x = _x
  ======================================================================
  codegen/pm-1_fails.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two = 2
  let two = _two
  let _three = 3
  let three = _three
  
  type intlist = IntNil | IntCons of (int * intlist);;
  
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
                  fun (() : unit) _k ->
                    Value
                      (_concat
                         (coer_arrow coer_refl_ty force_unsafe _k true)
                         (coer_arrow coer_refl_ty force_unsafe _k false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : intlist) -> Value _x))
       (let rec _f _x =
          Call (Decide, (), fun (_y : bool) -> Value (if _y then 2 else 3))
        in
        _f ()))
  ======================================================================
  codegen/pm-2_passes.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _two = 2
  let two = _two
  let _three = 3
  let three = _three
  
  type intlist = IntNil | IntCons of (int * intlist);;
  
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value (IntCons (_x, IntNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun (() : unit) _k ->
                    Value
                      (_concat
                         (coer_arrow coer_refl_ty force_unsafe _k true)
                         (coer_arrow coer_refl_ty force_unsafe _k false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : intlist) -> Value _x))
       (let rec _f _x =
          Call (Decide, (), fun (_y : bool) -> Value (if _y then 2 else 3))
        in
        _f ()))
  ======================================================================
  codegen/pm-3_passes.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  type intlist = IntNil | IntCons of (int * intlist);;
  
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value (IntCons (_x, IntNil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun (() : unit) _k ->
                    Value
                      (_concat
                         (coer_arrow coer_refl_ty force_unsafe _k true)
                         (coer_arrow coer_refl_ty force_unsafe _k false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : intlist) -> Value _x))
       (Call
          ( Decide,
            (),
            fun (_y : bool) ->
              Call
                ( Decide,
                  (),
                  fun (_y : bool) ->
                    Value ((if _y then 10 else 20) - if _y then 0 else 5) ) )))
  ======================================================================
  codegen/poly_bind.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _f (_ : 'ty) = 5
  let f = _f
  ======================================================================
  codegen/queens.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  type queen = int * int
  type rows = RowsEmpty | RowsCons of (int * rows)
  type solution = SolutionEmpty | SolutionPlace of ((int * int) * solution)
  type solutions = SolutionsNil | SolutionsCons of (solution * solutions)
  type optional_solution = None | Some of solution
  type void = Void
  
  let _absurd _tycoer (_void : 'ty) = match _tycoer _void with _ -> assert false
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
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : solution) -> Value (Some _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Decide ->
                    fun (_ : unit) _k ->
                      Value
                        (match coer_arrow coer_refl_ty force_unsafe _k true with
                        | Some _x -> Some _x
                        | None -> coer_arrow coer_refl_ty force_unsafe _k false)
                | Fail -> fun (_ : unit) __k -> Value None
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : optional_solution) -> Value _x))
         (_queens _number_of_queens))
  
  let queens_one_option = _queens_one_option
  
  let _queens_all (_number_of_queens : int) =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x : solution) -> Value (SolutionsCons (_x, SolutionsNil)));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Decide ->
                    fun (_ : unit) _k ->
                      Value
                        (_op (* @ *)
                           (coer_arrow coer_refl_ty force_unsafe _k true)
                           (coer_arrow coer_refl_ty force_unsafe _k false))
                | Fail -> fun (_ : unit) __k -> Value SolutionsNil
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : solutions) -> Value _x))
         (_queens _number_of_queens))
  
  let queens_all = _queens_all
  
  let _queens_one_cps (_number_of_queens : int) =
    force_unsafe
      ((handler
          {
            value_clause =
              (fun (_x : solution) ->
                Value
                  (coer_arrow coer_refl_ty (coer_return coer_refl_ty)
                     (fun (_ : unit -> solution computation) -> _x)));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Decide ->
                    fun (_ : unit) _k ->
                      Value
                        (fun (_kf : unit -> solution computation) ->
                          coer_arrow coer_refl_ty force_unsafe _k true
                            (fun (_ : unit) ->
                              coer_arrow coer_refl_ty force_unsafe _k false _kf))
                | Fail ->
                    fun (_ : unit) __k ->
                      Value (fun (_kf : unit -> solution computation) -> _kf ())
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : (unit -> solution computation) -> solution computation) ->
            Value _x))
         (_queens _number_of_queens))
      (fun (() : unit) ->
        Call
          (Fail, (), fun (_y : empty) -> Value (match _y with _ -> assert false)))
  
  let queens_one_cps = _queens_one_cps
  ======================================================================
  codegen/range.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Fetch : (unit, int) eff_internal_effect
  type int_list = Nil | Cons of (int * int_list)
  
  let _test (_n : int) =
    let rec _range _x =
      match _x with
      | 0 -> Value Nil
      | _ ->
          Call
            ( Fetch,
              (),
              fun (_y : int) ->
                _range (_x - 1) >>= fun _b -> Value (Cons (_y, _b)) )
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : int_list) -> Value _x);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Fetch ->
                    fun (_ : unit) _k ->
                      Value (coer_arrow coer_refl_ty force_unsafe _k 42)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int_list) -> Value _x))
         (_range _n))
  
  let test = _test
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorProduce : (int, int) eff_internal_effect
  
  let _testGenerator (_m : int) =
    let rec _sum _x =
      if _x = 0 then Call (GeneratorGet, (), fun (_y : int) -> Value _y)
      else
        Call
          ( GeneratorGet,
            (),
            fun (_y : int) ->
              Call
                ( GeneratorProduce,
                  _x,
                  fun (_y : int) ->
                    Call (GeneratorPut, _y + _y, fun (_y : unit) -> _sum (_x - 1))
                ) )
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : int) -> Value (fun (_ : int) -> _x));
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | GeneratorGet ->
                    fun (() : unit) _k ->
                      Value
                        (fun (_s : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k _s _s)
                | GeneratorPut ->
                    fun (_s : int) _k ->
                      Value
                        (fun (_ : int) ->
                          coer_arrow coer_refl_ty force_unsafe _k () _s)
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int -> int) -> Value _x))
         ((handler
             {
               value_clause = (fun (_id : int) -> Value _id);
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | GeneratorProduce -> fun (_i : int) _k -> _k (_i mod 42)
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : int) -> Value _x))
            (_sum _m)))
      _m
  
  let testGenerator = _testGenerator
  ======================================================================
  codegen/rec1.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  let rec _f _x = () in
  _f 1
  ======================================================================
  codegen/rec2.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  fun _tycoer -> 10
  ======================================================================
  codegen/redefine_local.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Ping : (unit, unit) eff_internal_effect
  
  let _test_simple (_x : 'ty) =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : unit * int) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Ping ->
                    fun (() : unit) _k ->
                      Value (coer_arrow coer_refl_ty force_unsafe _k ())
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : unit * int) -> Value _x))
         (Call (Ping, (), fun (_y : unit) -> Value (_y, 1))))
  
  let test_simple = _test_simple
  
  let _test_simple2 (() : unit) =
    force_unsafe
      ((handler
          {
            value_clause = (fun (_id : unit) -> Value _id);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Ping ->
                    fun (() : unit) _k ->
                      Value (coer_arrow coer_refl_ty force_unsafe _k ())
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : unit) -> Value _x))
         (Call (Ping, (), fun (_y : unit) -> Value _y)))
  
  let test_simple2 = _test_simple2
  ======================================================================
  codegen/reuse_toplevel_handler.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _h _tycoer _tycoer _tycoer _tycoer _tycoer _cmd =
    handler
      {
        value_clause =
          (fun (_x : 'ty) -> coer_return _tycoer (_tycoer (_tycoer _x)));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty) -> coer_return _tycoer (_tycoer _x))
      _cmd
  
  let h = _h;;
  
  coer_hand_to_fun coer_refl_ty force_unsafe
    (_h coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty)
    1
  ;;
  
  coer_hand_to_fun coer_refl_ty force_unsafe
    (_h coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty)
    (1, 2)
  ======================================================================
  codegen/substitution.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let _decide_func (_bl : bool) = if _bl then 10 else 20
  let decide_func = _decide_func
  ======================================================================
  codegen/test-handle_effect_skip.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  (handler
     {
       value_clause = (fun (_x : unit) -> Value 42);
       effect_clauses =
         (fun (type a b) (eff : (a, b) eff_internal_effect) : (a -> (b -> _) -> _) ->
           match eff with eff' -> fun arg k -> Call (eff', arg, k));
     }
     (fun (_x : int) -> Value _x))
    (Call (Print, "hello\n", fun (_y : unit) -> Value _y))
  ======================================================================
  codegen/test1.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test10.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test11.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect
  ======================================================================
  codegen/test12.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect;;
  
  handler
    {
      value_clause = (fun (_x : int) -> Value _x);
      effect_clauses =
        (fun (type a b) (eff : (a, b) eff_internal_effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Op1 -> fun (_n : int) _k -> Value 1
          | Op2 -> fun (_n : int) _k -> Value 2
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    (fun (_x : int) -> Value _x)
  ======================================================================
  codegen/test13.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op1 : (int, int) eff_internal_effect
  type (_, _) eff_internal_effect += Op2 : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op1 -> fun (_n : int) _k -> Value 1
              | Op2 -> fun (_n : int) _k -> Value 2
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Op1, 1, fun (_y : int) -> Call (Op2, 2, fun (_y : int) -> Value _y))))
  ======================================================================
  codegen/test14.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type integer = int
  type (_, _) eff_internal_effect += Op : (unit, int) eff_internal_effect;;
  
  fun (_y : int) -> Call (Op, (), fun (_y : int) -> Value (_y + _y))
  ======================================================================
  codegen/test15.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type foo = A | B of bar
  and bar = { x : foo }
  
  type (_, _) eff_internal_effect += Op1 : (int, bar) eff_internal_effect
  type (_, _) eff_internal_effect += Op2 : (bar, foo) eff_internal_effect
  type (_, _) eff_internal_effect += Op3 : (foo, int) eff_internal_effect;;
  
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
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect;;
  
  let rec _loop _x =
    if 0 < _x then
      Call
        ( Get,
          (),
          fun (_y : int) -> Call (Put, _y + 1, fun (_y : unit) -> _loop (_x - 1))
        )
    else Value ()
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : unit) -> Value (fun (_ : int) -> _x));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Get ->
                  fun (_ : unit) _k ->
                    Value
                      (fun (_s : int) ->
                        coer_arrow coer_refl_ty force_unsafe _k _s _s)
              | Put ->
                  fun (_s : int) _k ->
                    Value
                      (fun (_ : int) ->
                        coer_arrow coer_refl_ty force_unsafe _k () _s)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int -> unit) -> Value _x))
       (_loop 10))
    0
  ======================================================================
  codegen/test17.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type my_ty = Cons of my_ty;;
  
  fun (Cons _argmnt : my_ty) -> Cons _argmnt
  ======================================================================
  codegen/test18.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type nat = Zero | Succ of nat;;
  
  let rec _add _x (_x : nat) =
    match _x with Zero -> _x | Succ _n -> Succ (_add _x _n)
  in
  _add
  ======================================================================
  codegen/test19.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type nat = Zero | Succ of nat;;
  
  fun ((_w, _k, _num) : nat * nat * int) (_x : nat * nat * int) ->
    match _x with
    | Zero, Zero, 0 -> (_w, _k, Zero, 0, 0)
    | Zero, _z, _n -> (Zero, _z, Zero, _num, _n)
    | _x, Zero, _n -> (Zero, _w, _x, 1, _n)
    | _, _, _ -> (Zero, Zero, Zero, 0, 0)
  ======================================================================
  codegen/test2.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect
  ======================================================================
  codegen/test20.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  let rec _even _x = _x = 0 || _odd (_x - 1)
  and _odd _x = if _x = 0 then false else _even (_x - 1)
  
  let even, odd = (_even, _odd)
  ======================================================================
  codegen/test21.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  1, true
  ======================================================================
  codegen/test3.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  fun _tycoer _tycoer _tycoer _tycoer _tycoer ->
    handler
      {
        value_clause =
          (fun (_x : 'ty) -> coer_return _tycoer (_tycoer (_tycoer _x)));
        effect_clauses =
          (fun (type a b) (eff : (a, b) eff_internal_effect) :
               (a -> (b -> _) -> _) ->
            match eff with eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty) -> coer_return _tycoer (_tycoer _x))
  ======================================================================
  codegen/test4.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  ;;
  
  1
  ======================================================================
  codegen/test5.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect;;
  
  handler
    {
      value_clause = (fun (_id : int) -> Value _id);
      effect_clauses =
        (fun (type a b) (eff : (a, b) eff_internal_effect) : (a -> (b -> _) -> _) ->
          match eff with
          | Op -> fun (_n : int) _k -> Value 2
          | eff' -> fun arg k -> Call (eff', arg, k));
    }
    (fun (_x : int) -> Value _x)
  ======================================================================
  codegen/test6.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op -> fun (_n : int) _k -> Value 2
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Value 1))
  ======================================================================
  codegen/test7.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op -> fun (_n : int) _k -> Value 2
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Op, 1, fun (_y : int) -> Value _y)))
  ======================================================================
  codegen/test8.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op ->
                  fun (_n : int) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k 2)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Op, 1, fun (_y : int) -> Value _y)))
  ======================================================================
  codegen/test9.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Op : (int, int) eff_internal_effect;;
  
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value _x);
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Op ->
                  fun (_n : int) _k ->
                    Value (coer_arrow coer_refl_ty force_unsafe _k _n)
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int) -> Value _x))
       (Call (Op, 1, fun (_y : int) -> Value _y)))
  ======================================================================
  codegen/top-letrec_fails.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  type intlist = IntNil | IntCons of (int * intlist)
  
  let rec _concat _x (_x : intlist) =
    match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
  
  let concat = _concat;;
  
  IntNil
  ======================================================================
  codegen/tree.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
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
  
  let _max _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer (_a : 'ty) (_b : 'ty) =
    if
      coer_arrow _tycoer coer_refl_ty
        (coer_arrow _tycoer coer_refl_ty (( > ) (_tycoer _a)))
        (_tycoer _b)
    then _tycoer _a
    else _tycoer _b
  
  let max = _max
  
  let _effect_max (_m : int) =
    let rec _find_max _x =
      match _x with
      | Empty -> Value 0
      | Node (Empty, _x, Empty) -> Value _x
      | Node (_left, _x, _right) ->
          Call
            ( Choose,
              (),
              fun (_y : bool) ->
                (if _y then _find_max _left else _find_max _right)
                >>= fun _next -> Value (_x + _next) )
    in
    force_unsafe
      ((handler
          {
            value_clause = (fun (_x : int) -> Value _x);
            effect_clauses =
              (fun (type a b) (eff : (a, b) eff_internal_effect) :
                   (a -> (b -> _) -> _) ->
                match eff with
                | Choose ->
                    fun (() : unit) _k ->
                      Value
                        (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
                           coer_refl_ty coer_refl_ty
                           (coer_arrow coer_refl_ty force_unsafe _k true)
                           (coer_arrow coer_refl_ty force_unsafe _k false))
                | eff' -> fun arg k -> Call (eff', arg, k));
          }
          (fun (_x : int) -> Value _x))
         (_find_max (_tester _m)))
  
  let effect_max = _effect_max
  let _test_max (_m : int) = _effect_max _m
  let test_max = _test_max
  let _op (_x : int) (_y : int) = _x - (3 * _y)
  let op = _op
  
  let _max _tycoer _tycoer _tycoer _tycoer _tycoer _tycoer (_a : 'ty) (_b : 'ty) =
    if
      coer_arrow _tycoer coer_refl_ty
        (coer_arrow _tycoer coer_refl_ty (( > ) (_tycoer _a)))
        (_tycoer _b)
    then _tycoer _a
    else _tycoer _b
  
  let max = _max
  
  type intlist = Nil | Cons of (int * intlist)
  
  let rec _op (* @ *) _x (_ys : intlist) =
    match _x with Nil -> _ys | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
  
  let _op (* @ *) = _op (* @ *)
  
  let _test_general (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let rec _explore _x =
      match _x with
      | Empty -> Value 0
      | Node (_left, _x, _right) ->
          Call
            ( Choose,
              (),
              fun (_y : bool) ->
                (if _y then _explore _left >>= fun _b -> Value (_op _x _b)
                 else _explore _right >>= fun _b -> Value (_op _x _b))
                >>= fun _next -> Value _next )
    in
    _maxl 0
      (force_unsafe
         ((handler
             {
               value_clause = (fun (_x : int) -> Value (Cons (_x, Nil)));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Choose ->
                       fun (() : unit) _k ->
                         Value
                           (_op (* @ *)
                              (coer_arrow coer_refl_ty force_unsafe _k true)
                              (coer_arrow coer_refl_ty force_unsafe _k false))
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : intlist) -> Value _x))
            (_explore (_tester _m))))
  
  let test_general = _test_general
  
  let _test_general_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let ____t = _tester _m in
    let rec _explore _x =
      match _x with
      | Empty -> Value 0
      | Node (_left, _x, _right) ->
          Call
            ( Choose,
              (),
              fun (_y : bool) ->
                (if _y then _explore _left >>= fun _b -> Value (_op _x _b)
                 else _explore _right >>= fun _b -> Value (_op _x _b))
                >>= fun _next -> Value _next )
    in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (force_unsafe
                 ((handler
                     {
                       value_clause = (fun (_x : int) -> Value (Cons (_x, Nil)));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Choose ->
                               fun (() : unit) _k ->
                                 Value
                                   (_op (* @ *)
                                      (coer_arrow coer_refl_ty force_unsafe _k
                                         true)
                                      (coer_arrow coer_refl_ty force_unsafe _k
                                         false))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : intlist) -> Value _x))
                    (_explore ____t))))
    in
    _looper 100 0
  
  let test_general_loop = _test_general_loop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  let _absurd _tycoer (_void : 'ty) = match _tycoer _void with _ -> assert false
  let absurd = _absurd
  
  let _test_leaf_state (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Choose,
              (),
              fun (_y : bool) ->
                _explore (if _y then _left else _right) >>= fun _b ->
                Value (_op _x _b) )
    in
    _maxl 0
      (force_unsafe
         ((handler
             {
               value_clause =
                 (fun (_x : intlist) -> Value (fun (_ : intlist) -> _x));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Get ->
                       fun (() : unit) _k ->
                         Value
                           (fun (_s : intlist) ->
                             match _s with
                             | Cons (_x, _rest) ->
                                 coer_arrow coer_refl_ty force_unsafe _k _x _rest
                             | Nil -> Nil)
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : intlist -> intlist) -> Value _x))
            ((handler
                {
                  value_clause = (fun (_x : int) -> Value (Cons (_x, Nil)));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Choose ->
                          fun (() : unit) _k ->
                            _k true >>= fun _b ->
                            _k false >>= fun _b -> Value (_op (* @ *) _b _b)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                }
                (fun (_x : intlist) -> Value _x))
               (_explore (_tester _m))))
         (_populate_leafs 0 154))
  
  let test_leaf_state = _test_leaf_state
  
  let _test_leaf_state_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    let ____leafs = _populate_leafs 0 154 in
    let ____t = _tester _m in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Choose,
              (),
              fun (_y : bool) ->
                _explore (if _y then _left else _right) >>= fun _b ->
                Value (_op _x _b) )
    in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_x : intlist) -> Value (fun (_ : intlist) -> _x));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Get ->
                               fun (() : unit) _k ->
                                 Value
                                   (fun (_s : intlist) ->
                                     match _s with
                                     | Cons (_x, _rest) ->
                                         coer_arrow coer_refl_ty force_unsafe _k
                                           _x _rest
                                     | Nil -> Nil)
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : intlist -> intlist) -> Value _x))
                    ((handler
                        {
                          value_clause =
                            (fun (_x : int) -> Value (Cons (_x, Nil)));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Choose ->
                                  fun (() : unit) _k ->
                                    _k true >>= fun _b ->
                                    _k false >>= fun _b ->
                                    Value (_op (* @ *) _b _b)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        }
                        (fun (_x : intlist) -> Value _x))
                       (_explore ____t)))
                 ____leafs))
    in
    _looper 100 0
  
  let test_leaf_state_loop = _test_leaf_state_loop
  
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _test_leaf_state_update (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Set,
              _x * _x,
              fun (_y : unit) ->
                Call
                  ( Choose,
                    (),
                    fun (_y : bool) ->
                      _explore (if _y then _left else _right) >>= fun _b ->
                      Value (_op _x _b) ) )
    in
    _maxl 0
      (force_unsafe
         ((handler
             {
               value_clause = (fun (_x : intlist) -> Value (fun (_ : int) -> _x));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Get ->
                       fun (() : unit) _k ->
                         Value
                           (fun (_s : int) ->
                             coer_arrow coer_refl_ty force_unsafe _k _s _s)
                   | Set ->
                       fun (_s : int) _k ->
                         Value
                           (fun (_ : int) ->
                             coer_arrow coer_refl_ty force_unsafe _k () _s)
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : int -> intlist) -> Value _x))
            ((handler
                {
                  value_clause = (fun (_x : int) -> Value (Cons (_x, Nil)));
                  effect_clauses =
                    (fun (type a b) (eff : (a, b) eff_internal_effect) :
                         (a -> (b -> _) -> _) ->
                      match eff with
                      | Choose ->
                          fun (() : unit) _k ->
                            _k true >>= fun _b ->
                            _k false >>= fun _b -> Value (_op (* @ *) _b _b)
                      | eff' -> fun arg k -> Call (eff', arg, k));
                }
                (fun (_x : intlist) -> Value _x))
               (_explore (_tester _m))))
         (( ~- ) 1))
  
  let test_leaf_state_update = _test_leaf_state_update
  
  let _test_leaf_state_update_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let ____t = _tester _m in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Set,
              _x * _x,
              fun (_y : unit) ->
                Call
                  ( Choose,
                    (),
                    fun (_y : bool) ->
                      _explore (if _y then _left else _right) >>= fun _b ->
                      Value (_op _x _b) ) )
    in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_x : intlist) -> Value (fun (_ : int) -> _x));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Get ->
                               fun (() : unit) _k ->
                                 Value
                                   (fun (_s : int) ->
                                     coer_arrow coer_refl_ty force_unsafe _k _s _s)
                           | Set ->
                               fun (_s : int) _k ->
                                 Value
                                   (fun (_ : int) ->
                                     coer_arrow coer_refl_ty force_unsafe _k () _s)
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : int -> intlist) -> Value _x))
                    ((handler
                        {
                          value_clause =
                            (fun (_x : int) -> Value (Cons (_x, Nil)));
                          effect_clauses =
                            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                                 (a -> (b -> _) -> _) ->
                              match eff with
                              | Choose ->
                                  fun (() : unit) _k ->
                                    _k true >>= fun _b ->
                                    _k false >>= fun _b ->
                                    Value (_op (* @ *) _b _b)
                              | eff' -> fun arg k -> Call (eff', arg, k));
                        }
                        (fun (_x : intlist) -> Value _x))
                       (_explore ____t)))
                 (( ~- ) 1)))
    in
    _looper 100 0
  
  let test_leaf_state_update_loop = _test_leaf_state_update_loop
  
  let _test_leaf_state_update_merged_handler (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Set,
              _x * _x,
              fun (_y : unit) ->
                Call
                  ( Choose,
                    (),
                    fun (_y : bool) ->
                      _explore (if _y then _left else _right) >>= fun _b ->
                      Value (_op _x _b) ) )
    in
    _maxl 0
      (force_unsafe
         ((handler
             {
               value_clause =
                 (fun (_x : int) -> Value (fun (_ : int) -> Cons (_x, Nil)));
               effect_clauses =
                 (fun (type a b) (eff : (a, b) eff_internal_effect) :
                      (a -> (b -> _) -> _) ->
                   match eff with
                   | Get ->
                       fun (() : unit) _k ->
                         Value
                           (fun (_s : int) ->
                             coer_arrow coer_refl_ty force_unsafe _k _s _s)
                   | Set ->
                       fun (_s : int) _k ->
                         Value
                           (fun (_ : int) ->
                             coer_arrow coer_refl_ty force_unsafe _k () _s)
                   | Choose ->
                       fun (() : unit) _k ->
                         Value
                           (fun (_s : int) ->
                             _op (* @ *)
                               (coer_arrow coer_refl_ty force_unsafe _k true _s)
                               (coer_arrow coer_refl_ty force_unsafe _k false _s))
                   | eff' -> fun arg k -> Call (eff', arg, k));
             }
             (fun (_x : int -> intlist) -> Value _x))
            (_explore (_tester _m)))
         (( ~- ) 1))
  
  let test_leaf_state_update_merged_handler =
    _test_leaf_state_update_merged_handler
  
  let _test_leaf_state_update_merged_handler_loop (_m : int) =
    let rec _maxl _x (_x : intlist) =
      match _x with
      | Nil -> _x
      | Cons (_x, _xs) ->
          _maxl
            (_max coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty coer_refl_ty
               coer_refl_ty _x _x)
            _xs
    in
    let ____t = _tester _m in
    let rec _explore _x =
      match _x with
      | Empty -> Call (Get, (), fun (_y : int) -> Value _y)
      | Node (_left, _x, _right) ->
          Call
            ( Set,
              _x * _x,
              fun (_y : unit) ->
                Call
                  ( Choose,
                    (),
                    fun (_y : bool) ->
                      _explore (if _y then _left else _right) >>= fun _b ->
                      Value (_op _x _b) ) )
    in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        _looper (_x - 1)
          (_s
          + _maxl 0
              (force_unsafe
                 ((handler
                     {
                       value_clause =
                         (fun (_x : int) ->
                           Value (fun (_ : int) -> Cons (_x, Nil)));
                       effect_clauses =
                         (fun (type a b) (eff : (a, b) eff_internal_effect) :
                              (a -> (b -> _) -> _) ->
                           match eff with
                           | Get ->
                               fun (() : unit) _k ->
                                 Value
                                   (fun (_s : int) ->
                                     coer_arrow coer_refl_ty force_unsafe _k _s _s)
                           | Set ->
                               fun (_s : int) _k ->
                                 Value
                                   (fun (_ : int) ->
                                     coer_arrow coer_refl_ty force_unsafe _k () _s)
                           | Choose ->
                               fun (() : unit) _k ->
                                 Value
                                   (fun (_s : int) ->
                                     _op (* @ *)
                                       (coer_arrow coer_refl_ty force_unsafe _k
                                          true _s)
                                       (coer_arrow coer_refl_ty force_unsafe _k
                                          false _s))
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : int -> intlist) -> Value _x))
                    (_explore ____t))
                 (( ~- ) 1)))
    in
    _looper 100 0
  
  let test_leaf_state_update_merged_handler_loop =
    _test_leaf_state_update_merged_handler_loop
  ======================================================================
  codegen/two_inputs.eff
  ----------------------------------------------------------------------
  (* primitive effect *)
  type (_, _) eff_internal_effect += Print : (string, unit) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Read : (unit, string) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += Raise : (string, empty) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect += RandomInt : (int, int) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | RandomFloat : (float, float) eff_internal_effect
  
  (* primitive effect *)
  type (_, _) eff_internal_effect +=
    | Write : (string * string, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  type int_list = Nil | Cons of (int * int_list);;
  
  let rec _op (* @ *) _x (_ys : int_list) =
    match _x with Nil -> _ys | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
  in
  force_unsafe
    ((handler
        {
          value_clause = (fun (_x : int) -> Value (Cons (_x, Nil)));
          effect_clauses =
            (fun (type a b) (eff : (a, b) eff_internal_effect) :
                 (a -> (b -> _) -> _) ->
              match eff with
              | Decide ->
                  fun (() : unit) _k ->
                    Value
                      (_op (* @ *)
                         (coer_arrow coer_refl_ty force_unsafe _k true)
                         (coer_arrow coer_refl_ty force_unsafe _k false))
              | eff' -> fun arg k -> Call (eff', arg, k));
        }
        (fun (_x : int_list) -> Value _x))
       (Call (Decide, (), fun (_y : bool) -> Value (if _y then 10 else 20))))
-------------------------------------------------------------------------------
