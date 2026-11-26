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
  
  let _k = fun (_y : bool) -> if _y then 2 else 3 in
  _k true + _k false
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
    begin match _x with
    | TripleNil -> _ys
    | TripleCons (_x, _xs) -> TripleCons (_x, _op (* @ *) _xs _ys)
    end
  
  let _op (* @ *) = _op (* @ *)
  
  let _testTriple =
   fun (_n : int) (_s : int) ->
    let rec _choice _x =
      if _x < 1 then TripleNil
      else
        let _k =
         fun (_y : bool) ->
          if _y then
            let rec _choice _x =
              if _x < 1 then TripleNil
              else
                let _k =
                 fun (_y : bool) ->
                  if _y then
                    let rec _choice _x =
                      if _x < 1 then TripleNil
                      else
                        let _k =
                         fun (_y : bool) ->
                          if _y then
                            if _x + _x + _x = _s then
                              TripleCons ((_x, _x, _x), TripleNil)
                            else TripleNil
                          else _choice (_x - 1)
                        in
                        _op (* @ *) (_k true) (_k false)
                    in
                    _choice (_x - 1)
                  else _choice (_x - 1)
                in
                _op (* @ *) (_k true) (_k false)
            in
            _choice (_x - 1)
          else _choice (_x - 1)
        in
        _op (* @ *) (_k true) (_k false)
    in
    _choice _n
  
  let testTriple = _testTriple
  let _handleTripleWrap = fun ((_x, _y) : int * int) -> _testTriple _x _y
  let handleTripleWrap = _handleTripleWrap
  
  type queen = int * int
  type queen_list = Nil | Cons of ((int * int) * queen_list)
  type queen_list_list = QNil | QCons of (queen_list * queen_list_list)
  type intlist = End | Lst of (int * intlist)
  type option = Some of queen_list | None
  type (_, _) eff_internal_effect += Select : (intlist, int) eff_internal_effect
  
  let rec _filter _x (_x : intlist) =
    begin match _x with
    | End -> Value End
    | Lst (_x, _xs) ->
        _x _x >>= fun _b ->
        if _b then _filter _x _xs >>= fun _b -> Value (Lst (_x, _b))
        else _filter _x _xs
    end
  
  let filter = _filter
  
  let rec _forall _x (_x : queen_list) =
    begin match _x with
    | Nil -> Value true
    | Cons (_x, _xs) ->
        _x _x >>= fun _b -> if _b then _forall _x _xs else Value false
    end
  
  let forall = _forall
  
  let _no_attack =
   fun ((_x, _y) : int * int) ((_x', _y') : int * int) ->
    _x <> _x' && _y <> _y' && abs (_x - _x') <> abs (_y - _y')
  
  let no_attack = _no_attack
  
  let _available =
   fun (_x : int) (_qs : queen_list) (_l : intlist) ->
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
  
  let _find_solution =
   fun (_n : int) ->
    let rec _init _x (_acc : intlist) =
      if _x = 0 then _acc else _init (_x - 1) (Lst (_x, _acc))
    in
    let ____l = _init _n End in
    let rec _place (_x, _qs) =
      if _x = _n + 1 then Some _qs
      else
        let rec _loop _x (_x : intlist) =
          begin match _x with
          | End -> None
          | Lst (_x, _xs) ->
              begin match _x _x with None -> _loop _x _xs | Some _x -> Some _x
              end
          end
        in
        _loop
          (fun (_y : int) -> _place (_x + 1, Cons ((_x, _y), _qs)))
          (coer_arrow
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
             ____l)
    in
    _place (1, Nil)
  
  let find_solution = _find_solution
  let _queens_all = _find_solution
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
  
  let rec _handled_count _x (_s : int) =
    if _s = 0 then _s else _handled_count () (_s - 1)
  
  let _handled_count = _handled_count
  let _testCount = fun (_m : int) -> _handled_count () _m
  let testCount = _testCount
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorYield : (int, unit) eff_internal_effect
  
  let _testGenerator =
   fun (_n : int) ->
    let rec _generateFromTo (_l, _u) (_x : int) =
      if _l > _u then _x else _generateFromTo (_l + 1, _u) (_x + _l)
    in
    _generateFromTo (1, _n) 0
  
  let testGenerator = _testGenerator
  ======================================================================
  codegen/closed_handler.eff
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
  type (_, _) eff_internal_effect += Put : (int, unit) eff_internal_effect
  type (_, _) eff_internal_effect += Log : (int, unit) eff_internal_effect
  
  let _apply_h =
   fun (_h : int computation -> 'ty computation) ->
    _h (Call (Get, (), fun (_y : int) -> Value _y))
  
  let apply_h = _apply_h
  let _subsume = fun (_n : int) -> _n + 1
  let subsume = _subsume
  
  let _get_twice =
   fun (() : unit) ->
    Call
      ( Get,
        (),
        fun (_y : int) -> Call (Get, (), fun (_y : int) -> Value (_y + _y)) )
  
  let get_twice = _get_twice
  
  let _closed_impure =
   fun (_n : int) ->
    let _x = _n + _n in
    _x + _x
  
  let closed_impure = _closed_impure
  ======================================================================
  codegen/coercion_argument_order.eff
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
  
  type (_, _) eff_internal_effect += Tick : (unit, unit) eff_internal_effect
  
  let _compose =
   fun (_f : 'ty -> 'ty computation) (_g : 'ty -> 'ty computation) (_x : 'ty) ->
    _g _x >>= fun _b -> _f _b
  
  let compose = _compose
  let _test = fun (() : unit) -> 10 + (2 + 1)
  let test = _test
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
  
  let _compose =
   fun (_f : 'ty -> 'ty computation) (_g : 'ty -> 'ty computation) (_x : 'ty) ->
    _g _x >>= fun _b -> _f _b
  
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
  
  let _f =
   fun (_x : int) ->
    begin match _x with 1 -> 0 | _ -> 4
    end
  
  let f = _f
  
  let _g =
   fun (_a : a) ->
    ( begin match _a with
      | Nil -> 0
      | Cons (_x, Nil) -> _x + 4
      | Cons (4, _x) -> 7
      | _x -> 13
      end,
      0,
      3 + 4,
      13,
      7 )
  
  let g = _g
  ======================================================================
  codegen/generator.eff
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
  
  type (_, _) eff_internal_effect += Yield : (int, unit) eff_internal_effect
  type tree = Leaf | Node of (tree * int * tree)
  type generator = Empty | Thunk of (int * (unit -> generator))
  
  let rec _make _x =
    begin match _x with
    | 0 -> Leaf
    | _n ->
        let _t = _make (_n - 1) in
        Node (_t, _n, _t)
    end
  
  let make = _make
  
  let rec _iterate _x =
    begin match _x with
    | Leaf -> Value ()
    | Node (_l, _v, _r) ->
        _iterate _l >>= fun _ -> Call (Yield, _v, fun (_y : unit) -> _iterate _r)
    end
  
  let iterate = _iterate
  
  let _generate =
   fun (_f : unit -> 'ty computation) ->
    (closed_handler
       {
         value_clause = (fun (_x : 'ty) -> Empty);
         effect_clauses =
           (fun (type a)
             (type b)
             (eff : (a, b) eff_internal_effect)
             :
             (a -> (b -> _) -> _)
           ->
             match eff with
             | Yield -> fun (_x : int) _k -> Thunk (_x, _k)
             | _ -> fun _ _ -> assert false);
       }
       (fun (_x : generator) -> _x))
      (_f ())
  
  let generate = _generate
  
  let rec _sum _x (_x : generator) =
    begin match _x with Empty -> _x | Thunk (_v, _f) -> _sum (_v + _x) (_f ())
    end
  
  let sum = _sum
  let _x = _sum 0 (_generate (fun (() : unit) -> _iterate (_make 5)))
  let x = _x
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
  
  let _f =
   fun (_y : int_list) ->
    begin match _y with
    | Nil -> 1
    | Cons (_x, Nil) -> _x
    | Cons (_, Cons (_y, Nil)) -> _y
    | Cons (_x, _) -> _x
    end
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
  
  let rec _f _x = if _x = 0 then 1 else _f (_x - 1) * 2 in
  _f 5
  ;;
  
  let rec _g _x = if _x = 0 then 1 else _g (_x - 1) in
  _g 5
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
  
  1 + 3 + 2 + 4
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
  codegen/instantiate_in_list.eff
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
  
  let rec _map _x (_x : 'ty list) =
    begin match _x with
    | [] -> Value []
    | _x :: _xs ->
        _x _x >>= fun _b ->
        _map _x _xs >>= fun _b -> Value (_b :: _b)
    end
  
  let map = _map
  
  let _apply_all =
   fun (_fs : ('ty -> 'ty computation) list) (_x : 'ty) ->
    _map (fun (_f : 'ty -> 'ty computation) -> _f _x) _fs
  
  let apply_all = _apply_all
  
  let _test =
   fun (() : unit) ->
    coer_arrow
      (coer_list (coer_arrow coer_refl_ty (coer_return coer_refl_ty)))
      (coer_arrow coer_refl_ty force_unsafe)
      _apply_all
      [ (fun (_x : int) -> _x + 1); (fun (_x : int) -> 2 * _x) ]
      3
  
  let test = _test
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
    begin match _x with
    | 0 -> Sub (_addCase, _addCase)
    | _n -> Sub (_createZeroCase (_n - 1), _createZeroCase (_n - 1))
    end
  
  let createZeroCase = _createZeroCase
  
  let rec _createCase _x =
    begin match _x with
    | 1 -> Div (Num 100, _createZeroCase 3)
    | _ -> Add (_addCase, _createCase (_x - 1))
    end
  
  let createCase = _createCase
  
  let _bigTest =
   fun (_num : int) ->
    let rec _interp _x (_k : int -> int) =
      begin match _x with
      | Num _b -> _k _b
      | Add (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x + _y)))
      | Mul (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x * _y)))
      | Sub (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x - _y)))
      | Div (_l, _r) ->
          _interp _r (fun (_y : int) ->
              _interp _l (fun (_x : int) ->
                  begin match _y with 0 -> ( ~- ) 1 | _ -> _k (_x / _y)
                  end))
      end
    in
    _interp (_createCase _num) (fun (_id : int) -> _id)
  
  let bigTest = _bigTest
  
  let _bigTestLoop =
   fun (_num : int) ->
    let ____finalCase = _createCase _num in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _interp _x (_k : int -> int) =
          begin match _x with
          | Num _b -> _k _b
          | Add (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x + _y)))
          | Mul (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x * _y)))
          | Sub (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x - _y)))
          | Div (_l, _r) ->
              _interp _r (fun (_y : int) ->
                  _interp _l (fun (_x : int) ->
                      begin match _y with 0 -> ( ~- ) 1 | _ -> _k (_x / _y)
                      end))
          end
        in
        _looper (_x - 1) (_s + _interp ____finalCase (fun (_id : int) -> _id))
    in
    _looper 100 0
  
  let bigTestLoop = _bigTestLoop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _testState =
   fun (_n : int) ->
    let rec _interp _x (_k : int -> int -> int) =
      begin match _x with
      | Num _b -> fun (_ : int) -> _k _b (_b * _b)
      | Add (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x + _y)))
      | Mul (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x * _y)))
      | Sub (_l, _r) ->
          _interp _l (fun (_x : int) ->
              _interp _r (fun (_y : int) -> _k (_x - _y)))
      | Div (_l, _r) ->
          _interp _r (fun (_y : int) ->
              _interp _l (fun (_x : int) ->
                  begin match _y with
                  | 0 -> fun (_s : int) -> _k _s _s
                  | _ -> _k (_x / _y)
                  end))
      end
    in
    _interp (_createCase _n) (fun (_x : int) (_ : int) -> _x) _n
  
  let testState = _testState
  
  let _testStateLoop =
   fun (_n : int) ->
    let _addCase =
      Add
        ( Add (Add (Num 20, Num 2), Mul (Num 1, Num 2)),
          Sub (Add (Num 2, Num 2), Div (Num 1, Num 10)) )
    in
    let rec _createZeroCase _x =
      begin match _x with
      | 0 -> Sub (_addCase, _addCase)
      | _n -> Sub (_createZeroCase (_n - 1), _createZeroCase (_n - 1))
      end
    in
    let rec _createCase _x =
      begin match _x with
      | 1 -> Div (Num 100, _createZeroCase 3)
      | _ -> Add (_addCase, _createCase (_x - 1))
      end
    in
    let ____finalCase = _createCase _n in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _interp _x (_k : int -> int -> int) =
          begin match _x with
          | Num _b -> fun (_ : int) -> _k _b (_b * _b)
          | Add (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x + _y)))
          | Mul (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x * _y)))
          | Sub (_l, _r) ->
              _interp _l (fun (_x : int) ->
                  _interp _r (fun (_y : int) -> _k (_x - _y)))
          | Div (_l, _r) ->
              _interp _r (fun (_y : int) ->
                  _interp _l (fun (_x : int) ->
                      begin match _y with
                      | 0 -> fun (_s : int) -> _k _s _s
                      | _ -> _k (_x / _y)
                      end))
          end
        in
        _looper (_x - 1)
          (_s + _interp ____finalCase (fun (_x : int) (_ : int) -> _x) _n)
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
  
  Call (Op1, 1, fun (_y : unit) -> Value _y)
  ======================================================================
  codegen/lambda_lift_cast.eff
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
  
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  
  let _test =
   fun (_b : bool) ->
    if _b then Value (42 :: [])
    else Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false)
  
  let test = _test
  let _x = _test true
  let x = _x
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
  codegen/local_let_rec_effect.eff
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
  
  type (_, _) eff_internal_effect += Op : (int, unit) eff_internal_effect
  
  let _test =
   fun (_n : int) ->
    let rec _loop _x (_s : int) = if _x = 0 then _s else _loop (_x - 1) _s in
    _loop _n 0
  
  let test = _test
  let _x = _test 3
  let x = _x
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
  let _test_pure = _loop_pure
  let test_pure = _test_pure
  
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  
  let rec _loop_latent _x =
    if _x = 0 then Value ()
    else if _x < 0 then
      Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false)
    else _loop_latent (_x - 1)
  
  let loop_latent = _loop_latent
  let _test_latent = _loop_latent
  let test_latent = _test_latent
  
  type (_, _) eff_internal_effect += Incr : (unit, unit) eff_internal_effect
  
  let rec _loop_incr _x =
    if _x = 0 then Value ()
    else Call (Incr, (), fun (_y : unit) -> _loop_incr (_x - 1))
  
  let loop_incr = _loop_incr
  
  let rec _handled_loop_incr _x (_x : int) =
    if _x = 0 then _x else _handled_loop_incr (_x - 1) (_x + 1)
  
  let _handled_loop_incr = _handled_loop_incr
  let _test_incr = fun (_n : int) -> _handled_loop_incr _n 0
  let test_incr = _test_incr
  
  let rec _loop_incr' _x =
    if _x = 0 then Value ()
    else
      _loop_incr' (_x - 1) >>= fun _ ->
      Call (Incr, (), fun (_y : unit) -> Value _y)
  
  let loop_incr' = _loop_incr'
  
  let rec _handled_loop_incr' _x (_k : unit -> int -> int) =
    if _x = 0 then _k ()
    else
      _handled_loop_incr' (_x - 1) (fun (_ : unit) (_x : int) -> _k () (_x + 1))
  
  let _handled_loop_incr' = _handled_loop_incr'
  
  let _test_incr' =
   fun (_n : int) -> _handled_loop_incr' _n (fun (_x : unit) (_x : int) -> _x) 0
  
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
  
  let rec _handled_loop_state _x (_x : int) =
    if _x = 0 then _x else _handled_loop_state (_x - 1) (_x + 1)
  
  let _handled_loop_state = _handled_loop_state
  let _test_state = fun (_n : int) -> _handled_loop_state _n 0
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
  
  let rec _map _x (_x : 'ty list) =
    begin match _x with
    | [] -> Value []
    | _x :: _xs ->
        _x _x >>= fun _b ->
        _map _x _xs >>= fun _b -> Value (_b :: _b)
    end
  
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
  
  let _test_nested = fun (_m : int) -> _m
  let test_nested = _test_nested
  
  let _test_nested =
   fun (_m : int) ->
    let rec _go _x =
      if _x = 0 then Call (Fail, (), fun (_y : unit) -> Value _y)
      else
        let _k = fun (_y : bool) -> if _y then _go (_x - 1) else _go (_x - 2) in
        (closed_handler
           {
             value_clause = (fun (_id : unit) -> Value _id);
             effect_clauses =
               (fun (type a)
                 (type b)
                 (eff : (a, b) eff_internal_effect)
                 :
                 (a -> (b -> _) -> _)
               ->
                 match eff with
                 | Fail -> fun (() : unit) __k -> _k false
                 | _ -> fun _ _ -> assert false);
           }
           (fun (_x : unit computation) -> _x))
          (_k true)
    in
    _go _m
  
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
  
  let _f = fun (_x : 'ty) -> ()
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
  
  11
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
  
  let _k = fun (_y : bool) -> if _y then 10 else 20 in
  _k true + _k false
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
  
  let _k = fun (_b : int) ((_x, _y) : int * int) (_z : int) -> _x + _y + _z + _b
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
  
  let _a = fun (_b : bool) (_c : bool) -> _b && _c
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
  
  let rec _f _x = _x + if _x = 0 then 0 else _f (_x - 1) in
  _f 10
  ======================================================================
  codegen/parallel_dirt_edges.eff
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
  
  type (_, _) eff_internal_effect += A : (unit, unit) eff_internal_effect
  type (_, _) eff_internal_effect += B : (unit, unit) eff_internal_effect
  
  let _g =
   fun (_c : unit -> 'ty computation) (_b : bool) ->
    if _b then
      (handler
         {
           value_clause = (fun (_id : 'ty) -> Value _id);
           effect_clauses =
             (fun (type a)
               (type b)
               (eff : (a, b) eff_internal_effect)
               :
               (a -> (b -> _) -> _)
             ->
               match eff with
               | A -> fun (() : unit) _k -> _k ()
               | eff' -> fun arg k -> Call (eff', arg, k));
         }
         (fun (_x : 'ty) -> Value _x))
        (_c ())
    else
      (handler
         {
           value_clause = (fun (_id : 'ty) -> Value _id);
           effect_clauses =
             (fun (type a)
               (type b)
               (eff : (a, b) eff_internal_effect)
               :
               (a -> (b -> _) -> _)
             ->
               match eff with
               | B -> fun (() : unit) _k -> _k ()
               | eff' -> fun arg k -> Call (eff', arg, k));
         }
         (fun (_x : 'ty) -> Value _x))
        (_c ())
  
  let g = _g
  
  let _test =
   fun (() : unit) ->
    (closed_handler
       {
         value_clause = (fun (_id : int) -> _id);
         effect_clauses =
           (fun (type a)
             (type b)
             (eff : (a, b) eff_internal_effect)
             :
             (a -> (b -> _) -> _)
           ->
             match eff with
             | A -> fun (() : unit) _ -> 42
             | _ -> fun _ _ -> assert false);
       }
       (fun (_x : int) -> _x))
      (Call (A, (), fun (_y : unit) -> Value 1))
  
  let test = _test
  let _x = _test ()
  let x = _x
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
  
  let _absurd = fun (_void : 'ty) -> match _void with _ -> assert false
  let absurd = _absurd
  
  let rec _op (* @ *) _x (_ys : 'ty list) =
    begin match _x with [] -> _ys | _x :: _xs -> _x :: _op (* @ *) _xs _ys
    end
  
  let _op (* @ *) = _op (* @ *)
  
  type (_, _) eff_internal_effect += Symbol : (string, string) eff_internal_effect
  type (_, _) eff_internal_effect += Fail : (unit, empty) eff_internal_effect
  type (_, _) eff_internal_effect += Decide : (unit, bool) eff_internal_effect
  
  let _fail =
   fun (() : unit) ->
    Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false)
  
  let fail = _fail
  
  let _parse =
   fun _cmd ->
    handler
      {
        value_clause =
          (fun (_x : 'ty) ->
            Value
              (fun (_s : string list) ->
                begin match _s with [] -> Value _x | _ -> _fail ()
                end));
        effect_clauses =
          (fun (type a)
            (type b)
            (eff : (a, b) eff_internal_effect)
            :
            (a -> (b -> _) -> _)
          ->
            match eff with
            | Symbol ->
                fun (_c : string) _k ->
                  Value
                    (fun (_s : string list) ->
                      begin match _s with
                      | [] -> _fail ()
                      | _x :: _xs ->
                          if _c = _x then _k _x >>= fun _b -> _b _xs else _fail ()
                      end)
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : string list -> 'ty computation) -> Value _x)
      _cmd
  
  let parse = _parse
  
  let _allsols =
   fun _cmd ->
    handler
      {
        value_clause = (fun (_x : 'ty) -> Value (_x :: []));
        effect_clauses =
          (fun (type a)
            (type b)
            (eff : (a, b) eff_internal_effect)
            :
            (a -> (b -> _) -> _)
          ->
            match eff with
            | Decide ->
                fun (_ : unit) _k ->
                  _k true >>= fun _b ->
                  _k false >>= fun _b -> Value (_op (* @ *) _b _b)
            | Fail -> fun (_ : unit) _ -> Value []
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty list) -> Value _x)
      _cmd
  
  let allsols = _allsols
  
  let _backtrack =
   fun _cmd ->
    handler
      {
        value_clause = (fun (_id : 'ty) -> Value _id);
        effect_clauses =
          (fun (type a)
            (type b)
            (eff : (a, b) eff_internal_effect)
            :
            (a -> (b -> _) -> _)
          ->
            match eff with
            | Decide ->
                fun (_ : unit) _k ->
                  (handler
                     {
                       value_clause = (fun (_id : 'ty) -> Value _id);
                       effect_clauses =
                         (fun (type a)
                           (type b)
                           (eff : (a, b) eff_internal_effect)
                           :
                           (a -> (b -> _) -> _)
                         ->
                           match eff with
                           | Fail -> fun (_ : unit) _ -> _k false
                           | eff' -> fun arg k -> Call (eff', arg, k));
                     }
                     (fun (_x : 'ty) -> Value _x))
                    (_k true)
            | eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty) -> Value _x)
      _cmd
  
  let backtrack = _backtrack
  let _createNumber = fun ((_prev, _num) : int * int) -> (_prev * 10) + _num
  let createNumber = _createNumber
  
  let rec _parseNum (_l, _v) =
    begin match _l with
    | [] -> Value _v
    | _x :: _xs ->
        begin match _x with
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
        | _ -> _fail ()
        end
    end
  
  let parseNum = _parseNum
  let rec _toNum _x = _parseNum (_x, 0)
  let toNum = _toNum
  
  let _digit =
   fun (() : unit) ->
    let rec _checkNums _x =
      begin match _x with
      | [] -> _fail ()
      | _x :: _xs ->
          Call
            ( Decide,
              (),
              fun (_y : bool) ->
                if _y then Call (Symbol, _x, fun (_y : string) -> Value _y)
                else _checkNums _xs )
      end
    in
    _checkNums [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ]
  
  let digit = _digit
  
  let rec _many _x =
    Call (Decide, (), fun (_y : bool) -> if _y then _x () else Value [])
  
  let many = _many
  
  let rec _many1 _x =
    _digit () >>= fun _x ->
    _many _many1 >>= fun _xs -> Value (_op (* @ *) (_x :: []) _xs)
  
  let many1 = _many1
  
  let rec _expr _x =
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
  
  and _term _x =
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
  
  and _factor _x =
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
  
  let expr, term, factor = (_expr, _term, _factor)
  
  let rec _handled_many1 _x
      (_k : string list -> (string list -> int computation) computation) =
    let rec _checkNums _x =
      begin match _x with
      | [] ->
          Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false)
      | _x :: _xs ->
          Call
            ( Decide,
              (),
              fun (_y : bool) ->
                if _y then
                  Value
                    (fun (_s : string list) ->
                      begin match _s with
                      | [] -> _fail ()
                      | _x :: _xs ->
                          if _x = _x then
                            Call
                              ( Decide,
                                (),
                                fun (_y : bool) ->
                                  if _y then
                                    _handled_many1 () (fun (_xs : string list) ->
                                        _k (_op (* @ *) (_x :: []) _xs))
                                    >>= fun _b -> _b _xs
                                  else
                                    _k (_op (* @ *) (_x :: []) []) >>= fun _b ->
                                    _b _xs )
                          else _fail ()
                      end)
                else _checkNums _xs )
      end
    in
    _checkNums [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ]
  
  let _handled_many1 = _handled_many1
  
  let rec _handled_expr _x
      (_k : int -> (string list -> int computation) computation) =
    Call
      ( Decide,
        (),
        fun (_y : bool) ->
          if _y then
            _handled_term () (fun (_i : int) ->
                Value
                  (fun (_s : string list) ->
                    begin match _s with
                    | [] -> _fail ()
                    | _x :: _xs ->
                        if "+" = _x then
                          _handled_expr () (fun (_j : int) -> _k (_i + _j))
                          >>= fun _b -> _b _xs
                        else _fail ()
                    end))
          else _handled_term () _k )
  
  and _handled_term _x (_k : int -> (string list -> int computation) computation)
      =
    Call
      ( Decide,
        (),
        fun (_y : bool) ->
          if _y then
            _handled_factor () (fun (_i : int) ->
                Value
                  (fun (_s : string list) ->
                    begin match _s with
                    | [] -> _fail ()
                    | _x :: _xs ->
                        if "*" = _x then
                          _handled_term () (fun (_j : int) -> _k (_i * _j))
                          >>= fun _b -> _b _xs
                        else _fail ()
                    end))
          else _handled_factor () _k )
  
  and _handled_factor _x
      (_k : int -> (string list -> int computation) computation) =
    Call
      ( Decide,
        (),
        fun (_y : bool) ->
          if _y then
            _handled_many1 () (fun (_i : string list) ->
                _parseNum (_i, 0) >>= fun _y -> _k _y)
          else
            Value
              (fun (_s : string list) ->
                begin match _s with
                | [] -> _fail ()
                | _x :: _xs ->
                    if "(" = _x then
                      _handled_expr () (fun (_j : int) ->
                          Value
                            (fun (_s : string list) ->
                              begin match _s with
                              | [] -> _fail ()
                              | _x :: _xs ->
                                  if ")" = _x then _k _j >>= fun _b -> _b _xs
                                  else _fail ()
                              end))
                      >>= fun _b -> _b _xs
                    else _fail ()
                end) )
  
  let _handled_expr, _handled_term, _handled_factor =
    (_handled_expr, _handled_term, _handled_factor)
  
  let _parseTest =
   fun (() : unit) ->
    (closed_handler
       {
         value_clause =
           (fun (_b : string list -> int computation) ->
             (closed_handler
                {
                  value_clause = (fun (_x : int) -> _x :: []);
                  effect_clauses =
                    (fun (type a)
                      (type b)
                      (eff : (a, b) eff_internal_effect)
                      :
                      (a -> (b -> _) -> _)
                    ->
                      match eff with
                      | Decide ->
                          fun (_ : unit) _k -> _op (* @ *) (_k true) (_k false)
                      | Fail -> fun (_ : unit) _ -> []
                      | _ -> fun _ _ -> assert false);
                }
                (fun (_x : int list) -> _x))
               (_b [ "4"; "3"; "*"; "("; "3"; "+"; "3"; ")" ]));
         effect_clauses =
           (fun (type a)
             (type b)
             (eff : (a, b) eff_internal_effect)
             :
             (a -> (b -> _) -> _)
           ->
             match eff with
             | Decide -> fun (_ : unit) _k -> _op (* @ *) (_k true) (_k false)
             | Fail -> fun (_ : unit) _ -> []
             | _ -> fun _ _ -> assert false);
       }
       (fun (_x : int list) -> _x))
      (_handled_expr () (fun (_x : int) ->
           Value
             (fun (_s : string list) ->
               begin match _s with [] -> Value _x | _ -> _fail ()
               end)))
  
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
  
  let rec _concat _x (_x : intlist) =
    begin match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
    end
  in
  let _k =
   fun (_y : bool) -> if _y then IntCons (2, IntNil) else IntCons (3, IntNil)
  in
  _concat (_k true) (_k false)
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
    begin match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
    end
  in
  let _k =
   fun (_y : bool) -> if _y then IntCons (2, IntNil) else IntCons (3, IntNil)
  in
  _concat (_k true) (_k false)
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
    begin match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
    end
  in
  let _k =
   fun (_y : bool) ->
    if _y then
      let _k =
       fun (_y : bool) ->
        if _y then IntCons (10 - 0, IntNil) else IntCons (10 - 5, IntNil)
      in
      _concat (_k true) (_k false)
    else
      let _k =
       fun (_y : bool) ->
        if _y then IntCons (20 - 0, IntNil) else IntCons (20 - 5, IntNil)
      in
      _concat (_k true) (_k false)
  in
  _concat (_k true) (_k false)
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
  
  let _f = fun (_ : 'ty) -> 5
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
  
  let _absurd = fun (_void : 'ty) -> match _void with _ -> assert false
  let absurd = _absurd
  
  let rec _op (* @ *) _x (_ys : solutions) =
    begin match _x with
    | SolutionsNil -> _ys
    | SolutionsCons (_x, _xs) -> SolutionsCons (_x, _op (* @ *) _xs _ys)
    end
  
  let _op (* @ *) = _op (* @ *)
  
  let _no_attack =
   fun ((_x, _y) : int * int) ((_x', _y') : int * int) ->
    _x <> _x' && _y <> _y' && abs (_x - _x') <> abs (_y - _y')
  
  let no_attack = _no_attack
  
  let rec _not_attacked _x (_qs : solution) =
    begin match _qs with
    | SolutionEmpty -> true
    | SolutionPlace (_x, _xs) -> _no_attack _x _x && _not_attacked _x _xs
    end
  
  let not_attacked = _not_attacked
  
  let _available =
   fun (_number_of_queens : int) (_x : int) (_qs : solution) ->
    let rec _loop (_possible, _y) =
      if _y < 1 then _possible
      else if _not_attacked (_x, _y) _qs then
        _loop (RowsCons (_y, _possible), _y - 1)
      else _loop (_possible, _y - 1)
    in
    _loop (RowsEmpty, _number_of_queens)
  
  let available = _available
  
  let rec _choose _x =
    begin match _x with
    | RowsEmpty ->
        Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false)
    | RowsCons (_x, _xs') ->
        Call (Decide, (), fun (_y : bool) -> if _y then Value _x else _choose _xs')
    end
  
  let choose = _choose
  
  let _queens =
   fun (_number_of_queens : int) ->
    let rec _place (_x, _qs) =
      if _x > _number_of_queens then Value _qs
      else
        _choose (_available _number_of_queens _x _qs) >>= fun _y ->
        _place (_x + 1, SolutionPlace ((_x, _y), _qs))
    in
    _place (1, SolutionEmpty)
  
  let queens = _queens
  
  let rec _handled_choose _x (_k : int -> optional_solution) =
    begin match _x with
    | RowsEmpty -> None
    | RowsCons (_x, _xs') ->
        let _k =
         fun (_y : bool) -> if _y then _k _x else _handled_choose _xs' _k
        in
        begin match _k true with Some _x -> Some _x | None -> _k false
        end
    end
  
  let _handled_choose = _handled_choose
  
  let _queens_one_option =
   fun (_number_of_queens : int) ->
    let rec _place (_x, _qs) =
      if _x > _number_of_queens then Some _qs
      else
        let rec _loop (_possible, _y) =
          if _y < 1 then _possible
          else if _not_attacked (_x, _y) _qs then
            _loop (RowsCons (_y, _possible), _y - 1)
          else _loop (_possible, _y - 1)
        in
        _handled_choose
          (_loop (RowsEmpty, _number_of_queens))
          (fun (_y : int) -> _place (_x + 1, SolutionPlace ((_x, _y), _qs)))
    in
    _place (1, SolutionEmpty)
  
  let queens_one_option = _queens_one_option
  
  let rec _handled_choose _x (_k : int -> solutions) =
    begin match _x with
    | RowsEmpty -> SolutionsNil
    | RowsCons (_x, _xs') ->
        let _k =
         fun (_y : bool) -> if _y then _k _x else _handled_choose _xs' _k
        in
        _op (* @ *) (_k true) (_k false)
    end
  
  let _handled_choose = _handled_choose
  
  let _queens_all =
   fun (_number_of_queens : int) ->
    let rec _place (_x, _qs) =
      if _x > _number_of_queens then SolutionsCons (_qs, SolutionsNil)
      else
        let rec _loop (_possible, _y) =
          if _y < 1 then _possible
          else if _not_attacked (_x, _y) _qs then
            _loop (RowsCons (_y, _possible), _y - 1)
          else _loop (_possible, _y - 1)
        in
        _handled_choose
          (_loop (RowsEmpty, _number_of_queens))
          (fun (_y : int) -> _place (_x + 1, SolutionPlace ((_x, _y), _qs)))
    in
    _place (1, SolutionEmpty)
  
  let queens_all = _queens_all
  
  let rec _handled_choose _x
      (_k : int -> (unit -> solution computation) -> solution computation)
      (_x : unit -> solution computation) =
    begin match _x with
    | RowsEmpty -> _x ()
    | RowsCons (_x, _xs') ->
        let _k =
         fun (_y : bool) -> if _y then _k _x else _handled_choose _xs' _k
        in
        _k true (fun (_ : unit) -> _k false _x)
    end
  
  let _handled_choose = _handled_choose
  
  let _queens_one_cps =
   fun (_number_of_queens : int) ->
    let rec _place (_x, _qs) =
      if _x > _number_of_queens then
        coer_arrow coer_refl_ty (coer_return coer_refl_ty)
          (fun (_ : unit -> solution computation) -> _qs)
      else
        let rec _loop (_possible, _y) =
          if _y < 1 then _possible
          else if _not_attacked (_x, _y) _qs then
            _loop (RowsCons (_y, _possible), _y - 1)
          else _loop (_possible, _y - 1)
        in
        _handled_choose
          (_loop (RowsEmpty, _number_of_queens))
          (fun (_y : int) -> _place (_x + 1, SolutionPlace ((_x, _y), _qs)))
    in
    _place (1, SolutionEmpty) (fun (() : unit) ->
        Call (Fail, (), fun (_y : empty) -> match _y with _ -> assert false))
  
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
  
  let _test =
   fun (_n : int) ->
    let rec _range _x (_k : int_list -> int_list) =
      begin match _x with
      | 0 -> _k Nil
      | _ -> _range (_x - 1) (fun (_b : int_list) -> _k (Cons (42, _b)))
      end
    in
    _range _n (fun (_x : int_list) -> _x)
  
  let test = _test
  
  type (_, _) eff_internal_effect +=
    | GeneratorPut : (int, unit) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorGet : (unit, int) eff_internal_effect
  
  type (_, _) eff_internal_effect +=
    | GeneratorProduce : (int, int) eff_internal_effect
  
  let _testGenerator =
   fun (_m : int) ->
    let rec _sum _x (_x : int) =
      if _x = 0 then _x else _sum (_x - 1) (_x + (_x mod 42))
    in
    _sum _m _m
  
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
  
  ()
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
  
  10
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
  
  let _test_simple = fun (_x : 'ty) -> ((), 1)
  let test_simple = _test_simple
  let _test_simple2 = fun (() : unit) -> ()
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
  
  let _h =
   fun _cmd ->
    handler
      {
        value_clause = (fun (_x : 'ty) -> Value _x);
        effect_clauses =
          (fun (type a)
            (type b)
            (eff : (a, b) eff_internal_effect)
            :
            (a -> (b -> _) -> _)
          -> match eff with eff' -> fun arg k -> Call (eff', arg, k));
      }
      (fun (_x : 'ty) -> Value _x)
      _cmd
  
  let h = _h;;
  
  1;;
  1, 2
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
  
  let _decide_func = fun (_bl : bool) -> if _bl then 10 else 20
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
  
  Call (Print, "hello\n", fun (_y : unit) -> Value 42)
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
        (fun (type a)
          (type b)
          (eff : (a, b) eff_internal_effect)
          :
          (a -> (b -> _) -> _)
        ->
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
  
  1
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
  
  let rec _loop _x (_x : int) = if 0 < _x then _loop (_x - 1) (_x + 1) else () in
  _loop 10 0
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
    begin match _x with Zero -> _x | Succ _n -> Succ (_add _x _n)
    end
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
    begin match _x with
    | Zero, Zero, 0 -> (_w, _k, Zero, 0, 0)
    | Zero, _z, _n -> (Zero, _z, Zero, _num, _n)
    | _x, Zero, _n -> (Zero, _w, _x, 1, _n)
    | _, _, _ -> (Zero, Zero, Zero, 0, 0)
    end
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
  
  handler
    {
      value_clause = (fun (_x : 'ty) -> Value _x);
      effect_clauses =
        (fun (type a)
          (type b)
          (eff : (a, b) eff_internal_effect)
          :
          (a -> (b -> _) -> _)
        -> match eff with eff' -> fun arg k -> Call (eff', arg, k));
    }
    (fun (_x : 'ty) -> Value _x)
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
        (fun (type a)
          (type b)
          (eff : (a, b) eff_internal_effect)
          :
          (a -> (b -> _) -> _)
        ->
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
  
  1
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
  
  2
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
  
  2
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
  
  1
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
    begin match _x with
    | IntNil -> _x
    | IntCons (_z, _zs) -> IntCons (_z, _concat _zs _x)
    end
  
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
  
  let _tester =
   fun (_k : int) ->
    let _leaf = fun (_a : int) -> Node (Empty, _a * _k, Empty) in
    let _bot =
     fun (_t : tree) (_t2 : tree) ->
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
  let _max = fun (_a : 'ty) (_b : 'ty) -> if _a > _b then _a else _b
  let max = _max
  
  let _effect_max =
   fun (_m : int) ->
    let rec _find_max _x (_k : int -> int) =
      begin match _x with
      | Empty -> _k 0
      | Node (Empty, _x, Empty) -> _k _x
      | Node (_left, _x, _right) ->
          let _k =
           fun (_y : bool) ->
            if _y then _find_max _left (fun (_next : int) -> _k (_x + _next))
            else _find_max _right (fun (_next : int) -> _k (_x + _next))
          in
          _max (_k true) (_k false)
      end
    in
    _find_max (_tester _m) (fun (_x : int) -> _x)
  
  let effect_max = _effect_max
  let _test_max = _effect_max
  let test_max = _test_max
  let _op = fun (_x : int) (_y : int) -> _x - (3 * _y)
  let op = _op
  let _max = fun (_a : 'ty) (_b : 'ty) -> if _a > _b then _a else _b
  let max = _max
  
  type intlist = Nil | Cons of (int * intlist)
  
  let rec _op (* @ *) _x (_ys : intlist) =
    begin match _x with
    | Nil -> _ys
    | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
    end
  
  let _op (* @ *) = _op (* @ *)
  
  let _test_general =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let rec _explore _x (_k : int -> intlist) =
      begin match _x with
      | Empty -> _k 0
      | Node (_left, _x, _right) ->
          let _k =
           fun (_y : bool) ->
            if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b)))
            else _explore _right (fun (_b : int) -> _k (_x - (3 * _b)))
          in
          _op (* @ *) (_k true) (_k false)
      end
    in
    _maxl 0 (_explore (_tester _m) (fun (_x : int) -> Cons (_x, Nil)))
  
  let test_general = _test_general
  
  let _test_general_loop =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _explore _x (_k : int -> intlist) =
          begin match _x with
          | Empty -> _k 0
          | Node (_left, _x, _right) ->
              let _k =
               fun (_y : bool) ->
                if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b)))
                else _explore _right (fun (_b : int) -> _k (_x - (3 * _b)))
              in
              _op (* @ *) (_k true) (_k false)
          end
        in
        _looper (_x - 1)
          (_s + _maxl 0 (_explore ____t (fun (_x : int) -> Cons (_x, Nil))))
    in
    _looper 100 0
  
  let test_general_loop = _test_general_loop
  
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  
  let _absurd = fun (_void : 'ty) -> match _void with _ -> assert false
  let absurd = _absurd
  
  let _test_leaf_state =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    let rec _explore _x (_k : int -> intlist computation)
        (_k : intlist -> intlist -> intlist) =
      begin match _x with
      | Empty ->
          fun (_s : intlist) ->
            begin match _s with
            | Cons (_x, _rest) ->
                (closed_handler
                   {
                     value_clause = (fun (_y : intlist) -> _k _y);
                     effect_clauses =
                       (fun (type a)
                         (type b)
                         (eff : (a, b) eff_internal_effect)
                         :
                         (a -> (b -> _) -> _)
                       ->
                         match eff with
                         | Get ->
                             fun (() : unit) _k ->
                               fun (_s : intlist) ->
                                begin match _s with
                                | Cons (_x, _rest) -> _k _x _rest
                                | Nil -> Nil
                                end
                         | _ -> fun _ _ -> assert false);
                   }
                   (fun (_x : intlist -> intlist) -> _x))
                  (_k _x) _rest
            | Nil -> Nil
            end
      | Node (_left, _x, _right) ->
          let _k =
           fun (_y : bool) (_k : intlist -> intlist -> intlist) ->
            if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b))) _k
            else _explore _right (fun (_b : int) -> _k (_x - (3 * _b))) _k
          in
          _k true (fun (_b : intlist) ->
              _k false (fun (_b : intlist) -> _k (_op (* @ *) _b _b)))
      end
    in
    _maxl 0
      (_explore (_tester _m)
         (fun (_x : int) -> Value (Cons (_x, Nil)))
         (fun (_x : intlist) (_ : intlist) -> _x)
         (_populate_leafs 0 154))
  
  let test_leaf_state = _test_leaf_state
  
  let _test_leaf_state_loop =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let rec _populate_leafs _x (_n : int) =
      if _x = _n then Nil else Cons (_x * 3, _populate_leafs (_x + 1) _n)
    in
    let ____leafs = _populate_leafs 0 154 in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _explore _x (_k : int -> intlist computation)
            (_k : intlist -> intlist -> intlist) =
          begin match _x with
          | Empty ->
              fun (_s : intlist) ->
                begin match _s with
                | Cons (_x, _rest) ->
                    (closed_handler
                       {
                         value_clause = (fun (_y : intlist) -> _k _y);
                         effect_clauses =
                           (fun (type a)
                             (type b)
                             (eff : (a, b) eff_internal_effect)
                             :
                             (a -> (b -> _) -> _)
                           ->
                             match eff with
                             | Get ->
                                 fun (() : unit) _k ->
                                   fun (_s : intlist) ->
                                    begin match _s with
                                    | Cons (_x, _rest) -> _k _x _rest
                                    | Nil -> Nil
                                    end
                             | _ -> fun _ _ -> assert false);
                       }
                       (fun (_x : intlist -> intlist) -> _x))
                      (_k _x) _rest
                | Nil -> Nil
                end
          | Node (_left, _x, _right) ->
              let _k =
               fun (_y : bool) (_k : intlist -> intlist -> intlist) ->
                if _y then
                  _explore _left (fun (_b : int) -> _k (_x - (3 * _b))) _k
                else _explore _right (fun (_b : int) -> _k (_x - (3 * _b))) _k
              in
              _k true (fun (_b : intlist) ->
                  _k false (fun (_b : intlist) -> _k (_op (* @ *) _b _b)))
          end
        in
        _looper (_x - 1)
          (_s
          + _maxl 0
              (_explore ____t
                 (fun (_x : int) -> Value (Cons (_x, Nil)))
                 (fun (_x : intlist) (_ : intlist) -> _x)
                 ____leafs))
    in
    _looper 100 0
  
  let test_leaf_state_loop = _test_leaf_state_loop
  
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  
  let _test_leaf_state_update =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let rec _explore _x (_k : int -> intlist computation)
        (_k : intlist -> int -> intlist) (_x : int) =
      begin match _x with
      | Empty ->
          (closed_handler
             {
               value_clause = (fun (_y : intlist) -> _k _y);
               effect_clauses =
                 (fun (type a)
                   (type b)
                   (eff : (a, b) eff_internal_effect)
                   :
                   (a -> (b -> _) -> _)
                 ->
                   match eff with
                   | Get -> fun (() : unit) _k -> fun (_s : int) -> _k _s _s
                   | Set -> fun (_s : int) _k -> fun (_ : int) -> _k () _s
                   | _ -> fun _ _ -> assert false);
             }
             (fun (_x : int -> intlist) -> _x))
            (_k _x) _x
      | Node (_left, _x, _right) ->
          let _k =
           fun (_y : bool) (_k : intlist -> int -> intlist) ->
            if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b))) _k
            else _explore _right (fun (_b : int) -> _k (_x - (3 * _b))) _k
          in
          _k true
            (fun (_b : intlist) ->
              _k false (fun (_b : intlist) -> _k (_op (* @ *) _b _b)))
            (_x * _x)
      end
    in
    _maxl 0
      (_explore (_tester _m)
         (fun (_x : int) -> Value (Cons (_x, Nil)))
         (fun (_x : intlist) (_ : int) -> _x)
         (( ~- ) 1))
  
  let test_leaf_state_update = _test_leaf_state_update
  
  let _test_leaf_state_update_loop =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _explore _x (_k : int -> intlist computation)
            (_k : intlist -> int -> intlist) (_x : int) =
          begin match _x with
          | Empty ->
              (closed_handler
                 {
                   value_clause = (fun (_y : intlist) -> _k _y);
                   effect_clauses =
                     (fun (type a)
                       (type b)
                       (eff : (a, b) eff_internal_effect)
                       :
                       (a -> (b -> _) -> _)
                     ->
                       match eff with
                       | Get -> fun (() : unit) _k -> fun (_s : int) -> _k _s _s
                       | Set -> fun (_s : int) _k -> fun (_ : int) -> _k () _s
                       | _ -> fun _ _ -> assert false);
                 }
                 (fun (_x : int -> intlist) -> _x))
                (_k _x) _x
          | Node (_left, _x, _right) ->
              let _k =
               fun (_y : bool) (_k : intlist -> int -> intlist) ->
                if _y then
                  _explore _left (fun (_b : int) -> _k (_x - (3 * _b))) _k
                else _explore _right (fun (_b : int) -> _k (_x - (3 * _b))) _k
              in
              _k true
                (fun (_b : intlist) ->
                  _k false (fun (_b : intlist) -> _k (_op (* @ *) _b _b)))
                (_x * _x)
          end
        in
        _looper (_x - 1)
          (_s
          + _maxl 0
              (_explore ____t
                 (fun (_x : int) -> Value (Cons (_x, Nil)))
                 (fun (_x : intlist) (_ : int) -> _x)
                 (( ~- ) 1)))
    in
    _looper 100 0
  
  let test_leaf_state_update_loop = _test_leaf_state_update_loop
  
  let _test_leaf_state_update_merged_handler =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let rec _explore _x (_k : int -> int -> intlist) (_x : int) =
      begin match _x with
      | Empty -> _k _x _x
      | Node (_left, _x, _right) ->
          let _b = _x * _x in
          let _k =
           fun (_y : bool) ->
            if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b)))
            else _explore _right (fun (_b : int) -> _k (_x - (3 * _b)))
          in
          _op (* @ *) (_k true _b) (_k false _b)
      end
    in
    _maxl 0
      (_explore (_tester _m)
         (fun (_x : int) (_ : int) -> Cons (_x, Nil))
         (( ~- ) 1))
  
  let test_leaf_state_update_merged_handler =
    _test_leaf_state_update_merged_handler
  
  let _test_leaf_state_update_merged_handler_loop =
   fun (_m : int) ->
    let rec _maxl _x (_x : intlist) =
      begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
      end
    in
    let ____t = _tester _m in
    let rec _looper _x (_s : int) =
      if _x = 0 then _s
      else
        let rec _explore _x (_k : int -> int -> intlist) (_x : int) =
          begin match _x with
          | Empty -> _k _x _x
          | Node (_left, _x, _right) ->
              let _b = _x * _x in
              let _k =
               fun (_y : bool) ->
                if _y then _explore _left (fun (_b : int) -> _k (_x - (3 * _b)))
                else _explore _right (fun (_b : int) -> _k (_x - (3 * _b)))
              in
              _op (* @ *) (_k true _b) (_k false _b)
          end
        in
        _looper (_x - 1)
          (_s
          + _maxl 0
              (_explore ____t
                 (fun (_x : int) (_ : int) -> Cons (_x, Nil))
                 (( ~- ) 1)))
    in
    _looper 100 0
  
  let test_leaf_state_update_merged_handler_loop =
    _test_leaf_state_update_merged_handler_loop
  ======================================================================
  codegen/tree_explore_nested.eff
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
  
  type (_, _) eff_internal_effect += Choose : (unit, bool) eff_internal_effect
  type (_, _) eff_internal_effect += Get : (unit, int) eff_internal_effect
  type (_, _) eff_internal_effect += Set : (int, unit) eff_internal_effect
  type tree = Leaf | Node of (tree * int * tree)
  type intlist = Nil | Cons of (int * intlist)
  
  let _operator = fun (_x : int) (_y : int) -> abs (_x - (503 * _y) + 37) mod 1009
  let operator = _operator
  
  let rec _op (* @ *) _x (_ys : intlist) =
    begin match _x with
    | Nil -> _ys
    | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
    end
  
  let _op (* @ *) = _op (* @ *)
  
  let rec _make _x =
    begin match _x with
    | 0 -> Leaf
    | _n ->
        let _t = _make (_n - 1) in
        Node (_t, _n, _t)
    end
  
  let make = _make
  let _max = fun (_a : 'ty) (_b : 'ty) -> if _a > _b then _a else _b
  let max = _max
  
  let rec _maxl _x (_x : intlist) =
    begin match _x with Nil -> _x | Cons (_x, _xs) -> _maxl (_max _x _x) _xs
    end
  
  let maxl = _maxl
  
  let _run =
   fun (_n : int) ->
    let rec _loop _x =
      if _x = 0 then fun (_s : int) -> _s
      else
        let rec _explore _x (_k : int -> intlist computation)
            (_k : intlist -> int -> int) =
          begin match _x with
          | Leaf ->
              fun (_s : int) ->
                (closed_handler
                   {
                     value_clause = (fun (_y : intlist) -> _k _y);
                     effect_clauses =
                       (fun (type a)
                         (type b)
                         (eff : (a, b) eff_internal_effect)
                         :
                         (a -> (b -> _) -> _)
                       ->
                         match eff with
                         | Get -> fun (() : unit) _k -> fun (_s : int) -> _k _s _s
                         | Set -> fun (_s : int) _k -> fun (_ : int) -> _k () _s
                         | _ -> fun _ _ -> assert false);
                   }
                   (fun (_x : int -> int) -> _x))
                  (_k _s) _s
          | Node (_l, _v, _r) ->
              let _k =
               fun (_y : bool) (_k : intlist -> int -> int) (_x : int) ->
                if _y then
                  _explore _l
                    (fun (_b : int) -> _k (abs (_v - (503 * _b) + 37) mod 1009))
                    _k
                    (abs (_x - (503 * _v) + 37) mod 1009)
                else
                  _explore _r
                    (fun (_b : int) -> _k (abs (_v - (503 * _b) + 37) mod 1009))
                    _k
                    (abs (_x - (503 * _v) + 37) mod 1009)
              in
              _k true (fun (_b : intlist) ->
                  _k false (fun (_b : intlist) -> _k (_op (* @ *) _b _b)))
          end
        in
        _explore (_make _n)
          (fun (_x : int) -> Value (Cons (_x, Nil)))
          (fun (_b : intlist) (_ : int) -> _loop (_x - 1) (_maxl 0 _b))
    in
    _loop 10 0
  
  let run = _run
  let _x = _run 5
  let x = _x
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
    begin match _x with
    | Nil -> _ys
    | Cons (_x, _xs) -> Cons (_x, _op (* @ *) _xs _ys)
    end
  in
  let _k = fun (_y : bool) -> if _y then Cons (10, Nil) else Cons (20, Nil) in
  _op (* @ *) (_k true) (_k false)
-------------------------------------------------------------------------------
